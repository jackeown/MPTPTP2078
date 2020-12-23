%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:33 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  188 (1694 expanded)
%              Number of clauses        :  122 ( 536 expanded)
%              Number of leaves         :   15 ( 324 expanded)
%              Depth                    :   21
%              Number of atoms          :  642 (8064 expanded)
%              Number of equality atoms :  254 ( 791 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f68,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_709,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1198,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_711,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1196,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_2216,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1196])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_803,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2496,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_25,c_24,c_23,c_22,c_803])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_717,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1190,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2824,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_1190])).

cnf(c_26,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4388,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2824,c_26,c_27,c_28,c_29])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1195,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_4402,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_1195])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_714,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1193,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2100,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1193])).

cnf(c_795,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_797,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2458,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2100,c_26,c_27,c_28,c_29,c_797])).

cnf(c_2499,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2496,c_2458])).

cnf(c_6482,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4402,c_2499])).

cnf(c_6483,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_6482])).

cnf(c_6491,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_6483])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_328,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_329,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_345,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_329,c_6])).

cnf(c_705,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_relat_1(X0_48) = X1_49 ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_1202,plain,
    ( k2_relat_1(X0_48) = X0_49
    | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_4404,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_1202])).

cnf(c_706,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1201,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_724,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1183,plain,
    ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_1530,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1183])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_768,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_718,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_784,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48)
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1399,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1733,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_25,c_23,c_22,c_87,c_768,c_784,c_1399])).

cnf(c_4414,plain,
    ( k1_relat_1(sK1) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4404,c_1733])).

cnf(c_86,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_716,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1191,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2244,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1191])).

cnf(c_789,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_791,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_2581,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_26,c_27,c_28,c_29,c_791])).

cnf(c_2585,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2581,c_2496])).

cnf(c_1181,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_4403,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_1181])).

cnf(c_5042,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4414,c_88,c_2499,c_2585,c_4403])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_721,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1186,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1659,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1186])).

cnf(c_777,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1901,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_25,c_23,c_22,c_87,c_777,c_784,c_1399])).

cnf(c_5047,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_5042,c_1901])).

cnf(c_6517,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6491,c_5047])).

cnf(c_6629,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6517,c_26])).

cnf(c_3113,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1195])).

cnf(c_3296,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3113,c_26])).

cnf(c_3297,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3296])).

cnf(c_3305,plain,
    ( k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_3297])).

cnf(c_5280,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3305,c_795])).

cnf(c_5281,plain,
    ( k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5280])).

cnf(c_5291,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_5281])).

cnf(c_3609,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1202])).

cnf(c_811,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_3790,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_25,c_23,c_22,c_87,c_811,c_1399])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_722,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1185,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_1596,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1185])).

cnf(c_774,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1811,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_25,c_23,c_22,c_87,c_774,c_784,c_1399])).

cnf(c_3795,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3790,c_1811])).

cnf(c_5331,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5291,c_2496,c_3795])).

cnf(c_4393,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_3297])).

cnf(c_4483,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4393,c_3795])).

cnf(c_5345,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5331,c_2499,c_4483])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_710,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1197,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2500,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2496,c_1197])).

cnf(c_5348,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5345,c_2500])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_713,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1194,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_720,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1187,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1471,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1187])).

cnf(c_1478,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_5757,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5348,c_1478])).

cnf(c_6632,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6629,c_5757])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6632,c_1478])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:15:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.40/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.96  
% 3.40/0.96  ------  iProver source info
% 3.40/0.96  
% 3.40/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.96  git: non_committed_changes: false
% 3.40/0.96  git: last_make_outside_of_git: false
% 3.40/0.96  
% 3.40/0.96  ------ 
% 3.40/0.96  
% 3.40/0.96  ------ Input Options
% 3.40/0.96  
% 3.40/0.96  --out_options                           all
% 3.40/0.96  --tptp_safe_out                         true
% 3.40/0.96  --problem_path                          ""
% 3.40/0.96  --include_path                          ""
% 3.40/0.96  --clausifier                            res/vclausify_rel
% 3.40/0.96  --clausifier_options                    --mode clausify
% 3.40/0.96  --stdin                                 false
% 3.40/0.96  --stats_out                             all
% 3.40/0.96  
% 3.40/0.96  ------ General Options
% 3.40/0.96  
% 3.40/0.96  --fof                                   false
% 3.40/0.96  --time_out_real                         305.
% 3.40/0.96  --time_out_virtual                      -1.
% 3.40/0.96  --symbol_type_check                     false
% 3.40/0.96  --clausify_out                          false
% 3.40/0.96  --sig_cnt_out                           false
% 3.40/0.96  --trig_cnt_out                          false
% 3.40/0.96  --trig_cnt_out_tolerance                1.
% 3.40/0.96  --trig_cnt_out_sk_spl                   false
% 3.40/0.96  --abstr_cl_out                          false
% 3.40/0.96  
% 3.40/0.96  ------ Global Options
% 3.40/0.96  
% 3.40/0.96  --schedule                              default
% 3.40/0.96  --add_important_lit                     false
% 3.40/0.96  --prop_solver_per_cl                    1000
% 3.40/0.96  --min_unsat_core                        false
% 3.40/0.96  --soft_assumptions                      false
% 3.40/0.96  --soft_lemma_size                       3
% 3.40/0.96  --prop_impl_unit_size                   0
% 3.40/0.96  --prop_impl_unit                        []
% 3.40/0.96  --share_sel_clauses                     true
% 3.40/0.96  --reset_solvers                         false
% 3.40/0.96  --bc_imp_inh                            [conj_cone]
% 3.40/0.96  --conj_cone_tolerance                   3.
% 3.40/0.96  --extra_neg_conj                        none
% 3.40/0.96  --large_theory_mode                     true
% 3.40/0.96  --prolific_symb_bound                   200
% 3.40/0.96  --lt_threshold                          2000
% 3.40/0.96  --clause_weak_htbl                      true
% 3.40/0.96  --gc_record_bc_elim                     false
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing Options
% 3.40/0.97  
% 3.40/0.97  --preprocessing_flag                    true
% 3.40/0.97  --time_out_prep_mult                    0.1
% 3.40/0.97  --splitting_mode                        input
% 3.40/0.97  --splitting_grd                         true
% 3.40/0.97  --splitting_cvd                         false
% 3.40/0.97  --splitting_cvd_svl                     false
% 3.40/0.97  --splitting_nvd                         32
% 3.40/0.97  --sub_typing                            true
% 3.40/0.97  --prep_gs_sim                           true
% 3.40/0.97  --prep_unflatten                        true
% 3.40/0.97  --prep_res_sim                          true
% 3.40/0.97  --prep_upred                            true
% 3.40/0.97  --prep_sem_filter                       exhaustive
% 3.40/0.97  --prep_sem_filter_out                   false
% 3.40/0.97  --pred_elim                             true
% 3.40/0.97  --res_sim_input                         true
% 3.40/0.97  --eq_ax_congr_red                       true
% 3.40/0.97  --pure_diseq_elim                       true
% 3.40/0.97  --brand_transform                       false
% 3.40/0.97  --non_eq_to_eq                          false
% 3.40/0.97  --prep_def_merge                        true
% 3.40/0.97  --prep_def_merge_prop_impl              false
% 3.40/0.97  --prep_def_merge_mbd                    true
% 3.40/0.97  --prep_def_merge_tr_red                 false
% 3.40/0.97  --prep_def_merge_tr_cl                  false
% 3.40/0.97  --smt_preprocessing                     true
% 3.40/0.97  --smt_ac_axioms                         fast
% 3.40/0.97  --preprocessed_out                      false
% 3.40/0.97  --preprocessed_stats                    false
% 3.40/0.97  
% 3.40/0.97  ------ Abstraction refinement Options
% 3.40/0.97  
% 3.40/0.97  --abstr_ref                             []
% 3.40/0.97  --abstr_ref_prep                        false
% 3.40/0.97  --abstr_ref_until_sat                   false
% 3.40/0.97  --abstr_ref_sig_restrict                funpre
% 3.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.97  --abstr_ref_under                       []
% 3.40/0.97  
% 3.40/0.97  ------ SAT Options
% 3.40/0.97  
% 3.40/0.97  --sat_mode                              false
% 3.40/0.97  --sat_fm_restart_options                ""
% 3.40/0.97  --sat_gr_def                            false
% 3.40/0.97  --sat_epr_types                         true
% 3.40/0.97  --sat_non_cyclic_types                  false
% 3.40/0.97  --sat_finite_models                     false
% 3.40/0.97  --sat_fm_lemmas                         false
% 3.40/0.97  --sat_fm_prep                           false
% 3.40/0.97  --sat_fm_uc_incr                        true
% 3.40/0.97  --sat_out_model                         small
% 3.40/0.97  --sat_out_clauses                       false
% 3.40/0.97  
% 3.40/0.97  ------ QBF Options
% 3.40/0.97  
% 3.40/0.97  --qbf_mode                              false
% 3.40/0.97  --qbf_elim_univ                         false
% 3.40/0.97  --qbf_dom_inst                          none
% 3.40/0.97  --qbf_dom_pre_inst                      false
% 3.40/0.97  --qbf_sk_in                             false
% 3.40/0.97  --qbf_pred_elim                         true
% 3.40/0.97  --qbf_split                             512
% 3.40/0.97  
% 3.40/0.97  ------ BMC1 Options
% 3.40/0.97  
% 3.40/0.97  --bmc1_incremental                      false
% 3.40/0.97  --bmc1_axioms                           reachable_all
% 3.40/0.97  --bmc1_min_bound                        0
% 3.40/0.97  --bmc1_max_bound                        -1
% 3.40/0.97  --bmc1_max_bound_default                -1
% 3.40/0.97  --bmc1_symbol_reachability              true
% 3.40/0.97  --bmc1_property_lemmas                  false
% 3.40/0.97  --bmc1_k_induction                      false
% 3.40/0.97  --bmc1_non_equiv_states                 false
% 3.40/0.97  --bmc1_deadlock                         false
% 3.40/0.97  --bmc1_ucm                              false
% 3.40/0.97  --bmc1_add_unsat_core                   none
% 3.40/0.97  --bmc1_unsat_core_children              false
% 3.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.97  --bmc1_out_stat                         full
% 3.40/0.97  --bmc1_ground_init                      false
% 3.40/0.97  --bmc1_pre_inst_next_state              false
% 3.40/0.97  --bmc1_pre_inst_state                   false
% 3.40/0.97  --bmc1_pre_inst_reach_state             false
% 3.40/0.97  --bmc1_out_unsat_core                   false
% 3.40/0.97  --bmc1_aig_witness_out                  false
% 3.40/0.97  --bmc1_verbose                          false
% 3.40/0.97  --bmc1_dump_clauses_tptp                false
% 3.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.97  --bmc1_dump_file                        -
% 3.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.97  --bmc1_ucm_extend_mode                  1
% 3.40/0.97  --bmc1_ucm_init_mode                    2
% 3.40/0.97  --bmc1_ucm_cone_mode                    none
% 3.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.97  --bmc1_ucm_relax_model                  4
% 3.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.97  --bmc1_ucm_layered_model                none
% 3.40/0.97  --bmc1_ucm_max_lemma_size               10
% 3.40/0.97  
% 3.40/0.97  ------ AIG Options
% 3.40/0.97  
% 3.40/0.97  --aig_mode                              false
% 3.40/0.97  
% 3.40/0.97  ------ Instantiation Options
% 3.40/0.97  
% 3.40/0.97  --instantiation_flag                    true
% 3.40/0.97  --inst_sos_flag                         false
% 3.40/0.97  --inst_sos_phase                        true
% 3.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel_side                     num_symb
% 3.40/0.97  --inst_solver_per_active                1400
% 3.40/0.97  --inst_solver_calls_frac                1.
% 3.40/0.97  --inst_passive_queue_type               priority_queues
% 3.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.97  --inst_passive_queues_freq              [25;2]
% 3.40/0.97  --inst_dismatching                      true
% 3.40/0.97  --inst_eager_unprocessed_to_passive     true
% 3.40/0.97  --inst_prop_sim_given                   true
% 3.40/0.97  --inst_prop_sim_new                     false
% 3.40/0.97  --inst_subs_new                         false
% 3.40/0.97  --inst_eq_res_simp                      false
% 3.40/0.97  --inst_subs_given                       false
% 3.40/0.97  --inst_orphan_elimination               true
% 3.40/0.97  --inst_learning_loop_flag               true
% 3.40/0.97  --inst_learning_start                   3000
% 3.40/0.97  --inst_learning_factor                  2
% 3.40/0.97  --inst_start_prop_sim_after_learn       3
% 3.40/0.97  --inst_sel_renew                        solver
% 3.40/0.97  --inst_lit_activity_flag                true
% 3.40/0.97  --inst_restr_to_given                   false
% 3.40/0.97  --inst_activity_threshold               500
% 3.40/0.97  --inst_out_proof                        true
% 3.40/0.97  
% 3.40/0.97  ------ Resolution Options
% 3.40/0.97  
% 3.40/0.97  --resolution_flag                       true
% 3.40/0.97  --res_lit_sel                           adaptive
% 3.40/0.97  --res_lit_sel_side                      none
% 3.40/0.97  --res_ordering                          kbo
% 3.40/0.97  --res_to_prop_solver                    active
% 3.40/0.97  --res_prop_simpl_new                    false
% 3.40/0.97  --res_prop_simpl_given                  true
% 3.40/0.97  --res_passive_queue_type                priority_queues
% 3.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.97  --res_passive_queues_freq               [15;5]
% 3.40/0.97  --res_forward_subs                      full
% 3.40/0.97  --res_backward_subs                     full
% 3.40/0.97  --res_forward_subs_resolution           true
% 3.40/0.97  --res_backward_subs_resolution          true
% 3.40/0.97  --res_orphan_elimination                true
% 3.40/0.97  --res_time_limit                        2.
% 3.40/0.97  --res_out_proof                         true
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Options
% 3.40/0.97  
% 3.40/0.97  --superposition_flag                    true
% 3.40/0.97  --sup_passive_queue_type                priority_queues
% 3.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.97  --demod_completeness_check              fast
% 3.40/0.97  --demod_use_ground                      true
% 3.40/0.97  --sup_to_prop_solver                    passive
% 3.40/0.97  --sup_prop_simpl_new                    true
% 3.40/0.97  --sup_prop_simpl_given                  true
% 3.40/0.97  --sup_fun_splitting                     false
% 3.40/0.97  --sup_smt_interval                      50000
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Simplification Setup
% 3.40/0.97  
% 3.40/0.97  --sup_indices_passive                   []
% 3.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_full_bw                           [BwDemod]
% 3.40/0.97  --sup_immed_triv                        [TrivRules]
% 3.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_immed_bw_main                     []
% 3.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.97  
% 3.40/0.97  ------ Combination Options
% 3.40/0.97  
% 3.40/0.97  --comb_res_mult                         3
% 3.40/0.97  --comb_sup_mult                         2
% 3.40/0.97  --comb_inst_mult                        10
% 3.40/0.97  
% 3.40/0.97  ------ Debug Options
% 3.40/0.97  
% 3.40/0.97  --dbg_backtrace                         false
% 3.40/0.97  --dbg_dump_prop_clauses                 false
% 3.40/0.97  --dbg_dump_prop_clauses_file            -
% 3.40/0.97  --dbg_out_stat                          false
% 3.40/0.97  ------ Parsing...
% 3.40/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.97  ------ Proving...
% 3.40/0.97  ------ Problem Properties 
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  clauses                                 22
% 3.40/0.97  conjectures                             5
% 3.40/0.97  EPR                                     3
% 3.40/0.97  Horn                                    22
% 3.40/0.97  unary                                   6
% 3.40/0.97  binary                                  2
% 3.40/0.97  lits                                    72
% 3.40/0.97  lits eq                                 8
% 3.40/0.97  fd_pure                                 0
% 3.40/0.97  fd_pseudo                               0
% 3.40/0.97  fd_cond                                 0
% 3.40/0.97  fd_pseudo_cond                          2
% 3.40/0.97  AC symbols                              0
% 3.40/0.97  
% 3.40/0.97  ------ Schedule dynamic 5 is on 
% 3.40/0.97  
% 3.40/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  ------ 
% 3.40/0.97  Current options:
% 3.40/0.97  ------ 
% 3.40/0.97  
% 3.40/0.97  ------ Input Options
% 3.40/0.97  
% 3.40/0.97  --out_options                           all
% 3.40/0.97  --tptp_safe_out                         true
% 3.40/0.97  --problem_path                          ""
% 3.40/0.97  --include_path                          ""
% 3.40/0.97  --clausifier                            res/vclausify_rel
% 3.40/0.97  --clausifier_options                    --mode clausify
% 3.40/0.97  --stdin                                 false
% 3.40/0.97  --stats_out                             all
% 3.40/0.97  
% 3.40/0.97  ------ General Options
% 3.40/0.97  
% 3.40/0.97  --fof                                   false
% 3.40/0.97  --time_out_real                         305.
% 3.40/0.97  --time_out_virtual                      -1.
% 3.40/0.97  --symbol_type_check                     false
% 3.40/0.97  --clausify_out                          false
% 3.40/0.97  --sig_cnt_out                           false
% 3.40/0.97  --trig_cnt_out                          false
% 3.40/0.97  --trig_cnt_out_tolerance                1.
% 3.40/0.97  --trig_cnt_out_sk_spl                   false
% 3.40/0.97  --abstr_cl_out                          false
% 3.40/0.97  
% 3.40/0.97  ------ Global Options
% 3.40/0.97  
% 3.40/0.97  --schedule                              default
% 3.40/0.97  --add_important_lit                     false
% 3.40/0.97  --prop_solver_per_cl                    1000
% 3.40/0.97  --min_unsat_core                        false
% 3.40/0.97  --soft_assumptions                      false
% 3.40/0.97  --soft_lemma_size                       3
% 3.40/0.97  --prop_impl_unit_size                   0
% 3.40/0.97  --prop_impl_unit                        []
% 3.40/0.97  --share_sel_clauses                     true
% 3.40/0.97  --reset_solvers                         false
% 3.40/0.97  --bc_imp_inh                            [conj_cone]
% 3.40/0.97  --conj_cone_tolerance                   3.
% 3.40/0.97  --extra_neg_conj                        none
% 3.40/0.97  --large_theory_mode                     true
% 3.40/0.97  --prolific_symb_bound                   200
% 3.40/0.97  --lt_threshold                          2000
% 3.40/0.97  --clause_weak_htbl                      true
% 3.40/0.97  --gc_record_bc_elim                     false
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing Options
% 3.40/0.97  
% 3.40/0.97  --preprocessing_flag                    true
% 3.40/0.97  --time_out_prep_mult                    0.1
% 3.40/0.97  --splitting_mode                        input
% 3.40/0.97  --splitting_grd                         true
% 3.40/0.97  --splitting_cvd                         false
% 3.40/0.97  --splitting_cvd_svl                     false
% 3.40/0.97  --splitting_nvd                         32
% 3.40/0.97  --sub_typing                            true
% 3.40/0.97  --prep_gs_sim                           true
% 3.40/0.97  --prep_unflatten                        true
% 3.40/0.97  --prep_res_sim                          true
% 3.40/0.97  --prep_upred                            true
% 3.40/0.97  --prep_sem_filter                       exhaustive
% 3.40/0.97  --prep_sem_filter_out                   false
% 3.40/0.97  --pred_elim                             true
% 3.40/0.97  --res_sim_input                         true
% 3.40/0.97  --eq_ax_congr_red                       true
% 3.40/0.97  --pure_diseq_elim                       true
% 3.40/0.97  --brand_transform                       false
% 3.40/0.97  --non_eq_to_eq                          false
% 3.40/0.97  --prep_def_merge                        true
% 3.40/0.97  --prep_def_merge_prop_impl              false
% 3.40/0.97  --prep_def_merge_mbd                    true
% 3.40/0.97  --prep_def_merge_tr_red                 false
% 3.40/0.97  --prep_def_merge_tr_cl                  false
% 3.40/0.97  --smt_preprocessing                     true
% 3.40/0.97  --smt_ac_axioms                         fast
% 3.40/0.97  --preprocessed_out                      false
% 3.40/0.97  --preprocessed_stats                    false
% 3.40/0.97  
% 3.40/0.97  ------ Abstraction refinement Options
% 3.40/0.97  
% 3.40/0.97  --abstr_ref                             []
% 3.40/0.97  --abstr_ref_prep                        false
% 3.40/0.97  --abstr_ref_until_sat                   false
% 3.40/0.97  --abstr_ref_sig_restrict                funpre
% 3.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.97  --abstr_ref_under                       []
% 3.40/0.97  
% 3.40/0.97  ------ SAT Options
% 3.40/0.97  
% 3.40/0.97  --sat_mode                              false
% 3.40/0.97  --sat_fm_restart_options                ""
% 3.40/0.97  --sat_gr_def                            false
% 3.40/0.97  --sat_epr_types                         true
% 3.40/0.97  --sat_non_cyclic_types                  false
% 3.40/0.97  --sat_finite_models                     false
% 3.40/0.97  --sat_fm_lemmas                         false
% 3.40/0.97  --sat_fm_prep                           false
% 3.40/0.97  --sat_fm_uc_incr                        true
% 3.40/0.97  --sat_out_model                         small
% 3.40/0.97  --sat_out_clauses                       false
% 3.40/0.97  
% 3.40/0.97  ------ QBF Options
% 3.40/0.97  
% 3.40/0.97  --qbf_mode                              false
% 3.40/0.97  --qbf_elim_univ                         false
% 3.40/0.97  --qbf_dom_inst                          none
% 3.40/0.97  --qbf_dom_pre_inst                      false
% 3.40/0.97  --qbf_sk_in                             false
% 3.40/0.97  --qbf_pred_elim                         true
% 3.40/0.97  --qbf_split                             512
% 3.40/0.97  
% 3.40/0.97  ------ BMC1 Options
% 3.40/0.97  
% 3.40/0.97  --bmc1_incremental                      false
% 3.40/0.97  --bmc1_axioms                           reachable_all
% 3.40/0.97  --bmc1_min_bound                        0
% 3.40/0.97  --bmc1_max_bound                        -1
% 3.40/0.97  --bmc1_max_bound_default                -1
% 3.40/0.97  --bmc1_symbol_reachability              true
% 3.40/0.97  --bmc1_property_lemmas                  false
% 3.40/0.97  --bmc1_k_induction                      false
% 3.40/0.97  --bmc1_non_equiv_states                 false
% 3.40/0.97  --bmc1_deadlock                         false
% 3.40/0.97  --bmc1_ucm                              false
% 3.40/0.97  --bmc1_add_unsat_core                   none
% 3.40/0.97  --bmc1_unsat_core_children              false
% 3.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.97  --bmc1_out_stat                         full
% 3.40/0.97  --bmc1_ground_init                      false
% 3.40/0.97  --bmc1_pre_inst_next_state              false
% 3.40/0.97  --bmc1_pre_inst_state                   false
% 3.40/0.97  --bmc1_pre_inst_reach_state             false
% 3.40/0.97  --bmc1_out_unsat_core                   false
% 3.40/0.97  --bmc1_aig_witness_out                  false
% 3.40/0.97  --bmc1_verbose                          false
% 3.40/0.97  --bmc1_dump_clauses_tptp                false
% 3.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.97  --bmc1_dump_file                        -
% 3.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.97  --bmc1_ucm_extend_mode                  1
% 3.40/0.97  --bmc1_ucm_init_mode                    2
% 3.40/0.97  --bmc1_ucm_cone_mode                    none
% 3.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.97  --bmc1_ucm_relax_model                  4
% 3.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.97  --bmc1_ucm_layered_model                none
% 3.40/0.97  --bmc1_ucm_max_lemma_size               10
% 3.40/0.97  
% 3.40/0.97  ------ AIG Options
% 3.40/0.97  
% 3.40/0.97  --aig_mode                              false
% 3.40/0.97  
% 3.40/0.97  ------ Instantiation Options
% 3.40/0.97  
% 3.40/0.97  --instantiation_flag                    true
% 3.40/0.97  --inst_sos_flag                         false
% 3.40/0.97  --inst_sos_phase                        true
% 3.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel_side                     none
% 3.40/0.97  --inst_solver_per_active                1400
% 3.40/0.97  --inst_solver_calls_frac                1.
% 3.40/0.97  --inst_passive_queue_type               priority_queues
% 3.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.97  --inst_passive_queues_freq              [25;2]
% 3.40/0.97  --inst_dismatching                      true
% 3.40/0.97  --inst_eager_unprocessed_to_passive     true
% 3.40/0.97  --inst_prop_sim_given                   true
% 3.40/0.97  --inst_prop_sim_new                     false
% 3.40/0.97  --inst_subs_new                         false
% 3.40/0.97  --inst_eq_res_simp                      false
% 3.40/0.97  --inst_subs_given                       false
% 3.40/0.97  --inst_orphan_elimination               true
% 3.40/0.97  --inst_learning_loop_flag               true
% 3.40/0.97  --inst_learning_start                   3000
% 3.40/0.97  --inst_learning_factor                  2
% 3.40/0.97  --inst_start_prop_sim_after_learn       3
% 3.40/0.97  --inst_sel_renew                        solver
% 3.40/0.97  --inst_lit_activity_flag                true
% 3.40/0.97  --inst_restr_to_given                   false
% 3.40/0.97  --inst_activity_threshold               500
% 3.40/0.97  --inst_out_proof                        true
% 3.40/0.97  
% 3.40/0.97  ------ Resolution Options
% 3.40/0.97  
% 3.40/0.97  --resolution_flag                       false
% 3.40/0.97  --res_lit_sel                           adaptive
% 3.40/0.97  --res_lit_sel_side                      none
% 3.40/0.97  --res_ordering                          kbo
% 3.40/0.97  --res_to_prop_solver                    active
% 3.40/0.97  --res_prop_simpl_new                    false
% 3.40/0.97  --res_prop_simpl_given                  true
% 3.40/0.97  --res_passive_queue_type                priority_queues
% 3.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.97  --res_passive_queues_freq               [15;5]
% 3.40/0.97  --res_forward_subs                      full
% 3.40/0.97  --res_backward_subs                     full
% 3.40/0.97  --res_forward_subs_resolution           true
% 3.40/0.97  --res_backward_subs_resolution          true
% 3.40/0.97  --res_orphan_elimination                true
% 3.40/0.97  --res_time_limit                        2.
% 3.40/0.97  --res_out_proof                         true
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Options
% 3.40/0.97  
% 3.40/0.97  --superposition_flag                    true
% 3.40/0.97  --sup_passive_queue_type                priority_queues
% 3.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.97  --demod_completeness_check              fast
% 3.40/0.97  --demod_use_ground                      true
% 3.40/0.97  --sup_to_prop_solver                    passive
% 3.40/0.97  --sup_prop_simpl_new                    true
% 3.40/0.97  --sup_prop_simpl_given                  true
% 3.40/0.97  --sup_fun_splitting                     false
% 3.40/0.97  --sup_smt_interval                      50000
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Simplification Setup
% 3.40/0.97  
% 3.40/0.97  --sup_indices_passive                   []
% 3.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_full_bw                           [BwDemod]
% 3.40/0.97  --sup_immed_triv                        [TrivRules]
% 3.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_immed_bw_main                     []
% 3.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.97  
% 3.40/0.97  ------ Combination Options
% 3.40/0.97  
% 3.40/0.97  --comb_res_mult                         3
% 3.40/0.97  --comb_sup_mult                         2
% 3.40/0.97  --comb_inst_mult                        10
% 3.40/0.97  
% 3.40/0.97  ------ Debug Options
% 3.40/0.97  
% 3.40/0.97  --dbg_backtrace                         false
% 3.40/0.97  --dbg_dump_prop_clauses                 false
% 3.40/0.97  --dbg_dump_prop_clauses_file            -
% 3.40/0.97  --dbg_out_stat                          false
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  ------ Proving...
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  % SZS status Theorem for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  fof(f14,conjecture,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f15,negated_conjecture,(
% 3.40/0.97    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.40/0.97    inference(negated_conjecture,[],[f14])).
% 3.40/0.97  
% 3.40/0.97  fof(f36,plain,(
% 3.40/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f15])).
% 3.40/0.97  
% 3.40/0.97  fof(f37,plain,(
% 3.40/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f36])).
% 3.40/0.97  
% 3.40/0.97  fof(f40,plain,(
% 3.40/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.40/0.97    introduced(choice_axiom,[])).
% 3.40/0.97  
% 3.40/0.97  fof(f41,plain,(
% 3.40/0.97    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).
% 3.40/0.97  
% 3.40/0.97  fof(f67,plain,(
% 3.40/0.97    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.40/0.97    inference(cnf_transformation,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f12,axiom,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f34,plain,(
% 3.40/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f12])).
% 3.40/0.97  
% 3.40/0.97  fof(f35,plain,(
% 3.40/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f34])).
% 3.40/0.97  
% 3.40/0.97  fof(f62,plain,(
% 3.40/0.97    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f35])).
% 3.40/0.97  
% 3.40/0.97  fof(f64,plain,(
% 3.40/0.97    v1_funct_1(sK1)),
% 3.40/0.97    inference(cnf_transformation,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f65,plain,(
% 3.40/0.97    v1_funct_2(sK1,sK0,sK0)),
% 3.40/0.97    inference(cnf_transformation,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f66,plain,(
% 3.40/0.97    v3_funct_2(sK1,sK0,sK0)),
% 3.40/0.97    inference(cnf_transformation,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f9,axiom,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f30,plain,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f9])).
% 3.40/0.97  
% 3.40/0.97  fof(f31,plain,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f30])).
% 3.40/0.97  
% 3.40/0.97  fof(f59,plain,(
% 3.40/0.97    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f31])).
% 3.40/0.97  
% 3.40/0.97  fof(f11,axiom,(
% 3.40/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f32,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.40/0.97    inference(ennf_transformation,[],[f11])).
% 3.40/0.97  
% 3.40/0.97  fof(f33,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.40/0.97    inference(flattening,[],[f32])).
% 3.40/0.97  
% 3.40/0.97  fof(f61,plain,(
% 3.40/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f33])).
% 3.40/0.97  
% 3.40/0.97  fof(f56,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f31])).
% 3.40/0.97  
% 3.40/0.97  fof(f7,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f26,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(ennf_transformation,[],[f7])).
% 3.40/0.97  
% 3.40/0.97  fof(f27,plain,(
% 3.40/0.97    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(flattening,[],[f26])).
% 3.40/0.97  
% 3.40/0.97  fof(f53,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f27])).
% 3.40/0.97  
% 3.40/0.97  fof(f8,axiom,(
% 3.40/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f28,plain,(
% 3.40/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f8])).
% 3.40/0.97  
% 3.40/0.97  fof(f29,plain,(
% 3.40/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.40/0.97    inference(flattening,[],[f28])).
% 3.40/0.97  
% 3.40/0.97  fof(f39,plain,(
% 3.40/0.97    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.40/0.97    inference(nnf_transformation,[],[f29])).
% 3.40/0.97  
% 3.40/0.97  fof(f54,plain,(
% 3.40/0.97    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f39])).
% 3.40/0.97  
% 3.40/0.97  fof(f5,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f17,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.40/0.97    inference(pure_predicate_removal,[],[f5])).
% 3.40/0.97  
% 3.40/0.97  fof(f23,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(ennf_transformation,[],[f17])).
% 3.40/0.97  
% 3.40/0.97  fof(f48,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f23])).
% 3.40/0.97  
% 3.40/0.97  fof(f3,axiom,(
% 3.40/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f19,plain,(
% 3.40/0.97    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.40/0.97    inference(ennf_transformation,[],[f3])).
% 3.40/0.97  
% 3.40/0.97  fof(f20,plain,(
% 3.40/0.97    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.40/0.97    inference(flattening,[],[f19])).
% 3.40/0.97  
% 3.40/0.97  fof(f45,plain,(
% 3.40/0.97    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f20])).
% 3.40/0.97  
% 3.40/0.97  fof(f2,axiom,(
% 3.40/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f43,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f2])).
% 3.40/0.97  
% 3.40/0.97  fof(f52,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f27])).
% 3.40/0.97  
% 3.40/0.97  fof(f1,axiom,(
% 3.40/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f18,plain,(
% 3.40/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.40/0.97    inference(ennf_transformation,[],[f1])).
% 3.40/0.97  
% 3.40/0.97  fof(f42,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f18])).
% 3.40/0.97  
% 3.40/0.97  fof(f58,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f31])).
% 3.40/0.97  
% 3.40/0.97  fof(f4,axiom,(
% 3.40/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f21,plain,(
% 3.40/0.97    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.40/0.97    inference(ennf_transformation,[],[f4])).
% 3.40/0.97  
% 3.40/0.97  fof(f22,plain,(
% 3.40/0.97    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.40/0.97    inference(flattening,[],[f21])).
% 3.40/0.97  
% 3.40/0.97  fof(f46,plain,(
% 3.40/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f22])).
% 3.40/0.97  
% 3.40/0.97  fof(f13,axiom,(
% 3.40/0.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f63,plain,(
% 3.40/0.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f13])).
% 3.40/0.97  
% 3.40/0.97  fof(f70,plain,(
% 3.40/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(definition_unfolding,[],[f46,f63])).
% 3.40/0.97  
% 3.40/0.97  fof(f47,plain,(
% 3.40/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f22])).
% 3.40/0.97  
% 3.40/0.97  fof(f69,plain,(
% 3.40/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(definition_unfolding,[],[f47,f63])).
% 3.40/0.97  
% 3.40/0.97  fof(f68,plain,(
% 3.40/0.97    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.40/0.97    inference(cnf_transformation,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f10,axiom,(
% 3.40/0.97    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f16,plain,(
% 3.40/0.97    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.40/0.97    inference(pure_predicate_removal,[],[f10])).
% 3.40/0.97  
% 3.40/0.97  fof(f60,plain,(
% 3.40/0.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f16])).
% 3.40/0.97  
% 3.40/0.97  fof(f6,axiom,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f24,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.40/0.97    inference(ennf_transformation,[],[f6])).
% 3.40/0.97  
% 3.40/0.97  fof(f25,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(flattening,[],[f24])).
% 3.40/0.97  
% 3.40/0.97  fof(f38,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(nnf_transformation,[],[f25])).
% 3.40/0.97  
% 3.40/0.97  fof(f50,plain,(
% 3.40/0.97    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f38])).
% 3.40/0.97  
% 3.40/0.97  fof(f71,plain,(
% 3.40/0.97    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(equality_resolution,[],[f50])).
% 3.40/0.97  
% 3.40/0.97  cnf(c_22,negated_conjecture,
% 3.40/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_709,negated_conjecture,
% 3.40/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_22]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1198,plain,
% 3.40/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_20,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_711,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48)
% 3.40/0.97      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_20]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1196,plain,
% 3.40/0.97      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.40/0.97      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2216,plain,
% 3.40/0.97      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.40/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_1196]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_25,negated_conjecture,
% 3.40/0.97      ( v1_funct_1(sK1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_24,negated_conjecture,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_23,negated_conjecture,
% 3.40/0.97      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_803,plain,
% 3.40/0.97      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.40/0.97      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.40/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.40/0.97      | ~ v1_funct_1(sK1)
% 3.40/0.97      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_711]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2496,plain,
% 3.40/0.97      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_2216,c_25,c_24,c_23,c_22,c_803]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_14,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_717,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.40/0.97      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1190,plain,
% 3.40/0.97      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2824,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.40/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2496,c_1190]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_26,plain,
% 3.40/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_27,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_28,plain,
% 3.40/0.97      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_29,plain,
% 3.40/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4388,plain,
% 3.40/0.97      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_2824,c_26,c_27,c_28,c_29]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_19,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_funct_1(X3)
% 3.40/0.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_712,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.40/0.97      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48)
% 3.40/0.97      | ~ v1_funct_1(X1_48)
% 3.40/0.97      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_19]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1195,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(X1_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4402,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1))
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_4388,c_1195]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_17,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_714,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48)
% 3.40/0.97      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_17]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1193,plain,
% 3.40/0.97      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2100,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_1193]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_795,plain,
% 3.40/0.97      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_797,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_795]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2458,plain,
% 3.40/0.97      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_2100,c_26,c_27,c_28,c_29,c_797]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2499,plain,
% 3.40/0.97      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_2496,c_2458]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6482,plain,
% 3.40/0.97      ( v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1)) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_4402,c_2499]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6483,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,k2_funct_1(sK1)) = k5_relat_1(X0_48,k2_funct_1(sK1))
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_6482]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6491,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_6483]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_9,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | v2_funct_2(X0,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_13,plain,
% 3.40/0.97      ( ~ v2_funct_2(X0,X1)
% 3.40/0.97      | ~ v5_relat_1(X0,X1)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X1 ),
% 3.40/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_328,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ v5_relat_1(X3,X4)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X3)
% 3.40/0.97      | X3 != X0
% 3.40/0.97      | X4 != X2
% 3.40/0.97      | k2_relat_1(X3) = X4 ),
% 3.40/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_329,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ v5_relat_1(X0,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X2 ),
% 3.40/0.97      inference(unflattening,[status(thm)],[c_328]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6,plain,
% 3.40/0.97      ( v5_relat_1(X0,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_345,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X2 ),
% 3.40/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_329,c_6]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_705,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48)
% 3.40/0.97      | ~ v1_relat_1(X0_48)
% 3.40/0.97      | k2_relat_1(X0_48) = X1_49 ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_345]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1202,plain,
% 3.40/0.97      ( k2_relat_1(X0_48) = X0_49
% 3.40/0.97      | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_relat_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4404,plain,
% 3.40/0.97      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.40/0.97      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.40/0.97      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_4388,c_1202]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_706,negated_conjecture,
% 3.40/0.97      ( v1_funct_1(sK1) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_25]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1201,plain,
% 3.40/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v2_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_724,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0_48)
% 3.40/0.97      | ~ v2_funct_1(X0_48)
% 3.40/0.97      | ~ v1_relat_1(X0_48)
% 3.40/0.97      | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1183,plain,
% 3.40/0.97      ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v2_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_relat_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1530,plain,
% 3.40/0.97      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 3.40/0.97      | v2_funct_1(sK1) != iProver_top
% 3.40/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1201,c_1183]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_87,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_768,plain,
% 3.40/0.97      ( ~ v1_funct_1(sK1)
% 3.40/0.97      | ~ v2_funct_1(sK1)
% 3.40/0.97      | ~ v1_relat_1(sK1)
% 3.40/0.97      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_724]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_10,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | v2_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_718,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48)
% 3.40/0.97      | v2_funct_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_784,plain,
% 3.40/0.97      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.40/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.40/0.97      | ~ v1_funct_1(sK1)
% 3.40/0.97      | v2_funct_1(sK1) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_718]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_0,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/0.97      | ~ v1_relat_1(X1)
% 3.40/0.97      | v1_relat_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_726,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.40/0.97      | ~ v1_relat_1(X1_48)
% 3.40/0.97      | v1_relat_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1397,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.40/0.97      | v1_relat_1(X0_48)
% 3.40/0.97      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_726]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1399,plain,
% 3.40/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.40/0.97      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.40/0.97      | v1_relat_1(sK1) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1397]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1733,plain,
% 3.40/0.97      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_1530,c_25,c_23,c_22,c_87,c_768,c_784,c_1399]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4414,plain,
% 3.40/0.97      ( k1_relat_1(sK1) = sK0
% 3.40/0.97      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.40/0.97      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_4404,c_1733]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_86,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_88,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_86]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_15,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_716,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.40/0.97      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.40/0.97      | ~ v1_funct_1(X0_48) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_15]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1191,plain,
% 3.40/0.97      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2244,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_1191]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_789,plain,
% 3.40/0.97      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_791,plain,
% 3.40/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_789]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2581,plain,
% 3.40/0.97      ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_2244,c_26,c_27,c_28,c_29,c_791]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2585,plain,
% 3.40/0.97      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
% 3.40/0.97      inference(light_normalisation,[status(thm)],[c_2581,c_2496]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1181,plain,
% 3.40/0.97      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 3.40/0.97      | v1_relat_1(X1_48) != iProver_top
% 3.40/0.97      | v1_relat_1(X0_48) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4403,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.40/0.97      | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_4388,c_1181]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5042,plain,
% 3.40/0.97      ( k1_relat_1(sK1) = sK0 ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_4414,c_88,c_2499,c_2585,c_4403]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v2_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_721,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0_48)
% 3.40/0.97      | ~ v2_funct_1(X0_48)
% 3.40/0.97      | ~ v1_relat_1(X0_48)
% 3.40/0.97      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1186,plain,
% 3.40/0.97      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v2_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_relat_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1659,plain,
% 3.40/0.97      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.40/0.97      | v2_funct_1(sK1) != iProver_top
% 3.40/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1201,c_1186]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_777,plain,
% 3.40/0.97      ( ~ v1_funct_1(sK1)
% 3.40/0.97      | ~ v2_funct_1(sK1)
% 3.40/0.97      | ~ v1_relat_1(sK1)
% 3.40/0.97      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_721]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1901,plain,
% 3.40/0.97      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_1659,c_25,c_23,c_22,c_87,c_777,c_784,c_1399]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5047,plain,
% 3.40/0.97      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_5042,c_1901]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6517,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(light_normalisation,[status(thm)],[c_6491,c_5047]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6629,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_6517,c_26]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3113,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_1195]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3296,plain,
% 3.40/0.97      ( v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_3113,c_26]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3297,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_3296]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3305,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1)
% 3.40/0.97      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1190,c_3297]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5280,plain,
% 3.40/0.97      ( v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_3305,c_795]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5281,plain,
% 3.40/0.97      ( k1_partfun1(X0_49,X0_49,sK0,sK0,k2_funct_2(X0_49,X0_48),sK1) = k5_relat_1(k2_funct_2(X0_49,X0_48),sK1)
% 3.40/0.97      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_5280]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5291,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.40/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_5281]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3609,plain,
% 3.40/0.97      ( k2_relat_1(sK1) = sK0
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top
% 3.40/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1198,c_1202]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_811,plain,
% 3.40/0.97      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.40/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.40/0.97      | ~ v1_funct_1(sK1)
% 3.40/0.97      | ~ v1_relat_1(sK1)
% 3.40/0.97      | k2_relat_1(sK1) = sK0 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_705]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3790,plain,
% 3.40/0.97      ( k2_relat_1(sK1) = sK0 ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_3609,c_25,c_23,c_22,c_87,c_811,c_1399]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v2_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_722,plain,
% 3.40/0.97      ( ~ v1_funct_1(X0_48)
% 3.40/0.97      | ~ v2_funct_1(X0_48)
% 3.40/0.97      | ~ v1_relat_1(X0_48)
% 3.40/0.97      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1185,plain,
% 3.40/0.97      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.40/0.97      | v1_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v2_funct_1(X0_48) != iProver_top
% 3.40/0.97      | v1_relat_1(X0_48) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1596,plain,
% 3.40/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.40/0.97      | v2_funct_1(sK1) != iProver_top
% 3.40/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1201,c_1185]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_774,plain,
% 3.40/0.97      ( ~ v1_funct_1(sK1)
% 3.40/0.97      | ~ v2_funct_1(sK1)
% 3.40/0.97      | ~ v1_relat_1(sK1)
% 3.40/0.97      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_722]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1811,plain,
% 3.40/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_1596,c_25,c_23,c_22,c_87,c_774,c_784,c_1399]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3795,plain,
% 3.40/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_3790,c_1811]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5331,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.40/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.40/0.97      inference(light_normalisation,[status(thm)],[c_5291,c_2496,c_3795]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4393,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.40/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_4388,c_3297]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4483,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.40/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.40/0.97      inference(light_normalisation,[status(thm)],[c_4393,c_3795]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5345,plain,
% 3.40/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_5331,c_2499,c_4483]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_21,negated_conjecture,
% 3.40/0.97      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.40/0.97      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_710,negated_conjecture,
% 3.40/0.97      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.40/0.97      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_21]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1197,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.40/0.97      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2500,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.40/0.97      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_2496,c_1197]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5348,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.40/0.97      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_5345,c_2500]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_18,plain,
% 3.40/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_713,plain,
% 3.40/0.97      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_18]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1194,plain,
% 3.40/0.97      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_7,plain,
% 3.40/0.97      ( r2_relset_1(X0,X1,X2,X2)
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_720,plain,
% 3.40/0.97      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.40/0.97      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.40/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1187,plain,
% 3.40/0.97      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.40/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1471,plain,
% 3.40/0.97      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_1194,c_1187]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1478,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1471]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5757,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_5348,c_1478]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6632,plain,
% 3.40/0.97      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_6629,c_5757]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(contradiction,plain,
% 3.40/0.97      ( $false ),
% 3.40/0.97      inference(minisat,[status(thm)],[c_6632,c_1478]) ).
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  ------                               Statistics
% 3.40/0.97  
% 3.40/0.97  ------ General
% 3.40/0.97  
% 3.40/0.97  abstr_ref_over_cycles:                  0
% 3.40/0.97  abstr_ref_under_cycles:                 0
% 3.40/0.97  gc_basic_clause_elim:                   0
% 3.40/0.97  forced_gc_time:                         0
% 3.40/0.97  parsing_time:                           0.01
% 3.40/0.97  unif_index_cands_time:                  0.
% 3.40/0.97  unif_index_add_time:                    0.
% 3.40/0.97  orderings_time:                         0.
% 3.40/0.97  out_proof_time:                         0.011
% 3.40/0.97  total_time:                             0.245
% 3.40/0.97  num_of_symbols:                         54
% 3.40/0.97  num_of_terms:                           5530
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing
% 3.40/0.97  
% 3.40/0.97  num_of_splits:                          0
% 3.40/0.97  num_of_split_atoms:                     0
% 3.40/0.97  num_of_reused_defs:                     0
% 3.40/0.97  num_eq_ax_congr_red:                    8
% 3.40/0.97  num_of_sem_filtered_clauses:            1
% 3.40/0.97  num_of_subtypes:                        3
% 3.40/0.97  monotx_restored_types:                  1
% 3.40/0.97  sat_num_of_epr_types:                   0
% 3.40/0.97  sat_num_of_non_cyclic_types:            0
% 3.40/0.97  sat_guarded_non_collapsed_types:        1
% 3.40/0.97  num_pure_diseq_elim:                    0
% 3.40/0.97  simp_replaced_by:                       0
% 3.40/0.97  res_preprocessed:                       130
% 3.40/0.97  prep_upred:                             0
% 3.40/0.97  prep_unflattend:                        6
% 3.40/0.97  smt_new_axioms:                         0
% 3.40/0.97  pred_elim_cands:                        7
% 3.40/0.97  pred_elim:                              2
% 3.40/0.97  pred_elim_cl:                           3
% 3.40/0.97  pred_elim_cycles:                       5
% 3.40/0.97  merged_defs:                            0
% 3.40/0.97  merged_defs_ncl:                        0
% 3.40/0.97  bin_hyper_res:                          0
% 3.40/0.97  prep_cycles:                            4
% 3.40/0.97  pred_elim_time:                         0.006
% 3.40/0.97  splitting_time:                         0.
% 3.40/0.97  sem_filter_time:                        0.
% 3.40/0.97  monotx_time:                            0.001
% 3.40/0.97  subtype_inf_time:                       0.001
% 3.40/0.97  
% 3.40/0.97  ------ Problem properties
% 3.40/0.97  
% 3.40/0.97  clauses:                                22
% 3.40/0.97  conjectures:                            5
% 3.40/0.97  epr:                                    3
% 3.40/0.97  horn:                                   22
% 3.40/0.97  ground:                                 5
% 3.40/0.97  unary:                                  6
% 3.40/0.97  binary:                                 2
% 3.40/0.97  lits:                                   72
% 3.40/0.97  lits_eq:                                8
% 3.40/0.97  fd_pure:                                0
% 3.40/0.97  fd_pseudo:                              0
% 3.40/0.97  fd_cond:                                0
% 3.40/0.97  fd_pseudo_cond:                         2
% 3.40/0.97  ac_symbols:                             0
% 3.40/0.97  
% 3.40/0.97  ------ Propositional Solver
% 3.40/0.97  
% 3.40/0.97  prop_solver_calls:                      30
% 3.40/0.97  prop_fast_solver_calls:                 1207
% 3.40/0.97  smt_solver_calls:                       0
% 3.40/0.97  smt_fast_solver_calls:                  0
% 3.40/0.97  prop_num_of_clauses:                    1849
% 3.40/0.97  prop_preprocess_simplified:             6443
% 3.40/0.97  prop_fo_subsumed:                       66
% 3.40/0.97  prop_solver_time:                       0.
% 3.40/0.97  smt_solver_time:                        0.
% 3.40/0.97  smt_fast_solver_time:                   0.
% 3.40/0.97  prop_fast_solver_time:                  0.
% 3.40/0.97  prop_unsat_core_time:                   0.
% 3.40/0.97  
% 3.40/0.97  ------ QBF
% 3.40/0.97  
% 3.40/0.97  qbf_q_res:                              0
% 3.40/0.97  qbf_num_tautologies:                    0
% 3.40/0.97  qbf_prep_cycles:                        0
% 3.40/0.97  
% 3.40/0.97  ------ BMC1
% 3.40/0.97  
% 3.40/0.97  bmc1_current_bound:                     -1
% 3.40/0.97  bmc1_last_solved_bound:                 -1
% 3.40/0.97  bmc1_unsat_core_size:                   -1
% 3.40/0.97  bmc1_unsat_core_parents_size:           -1
% 3.40/0.97  bmc1_merge_next_fun:                    0
% 3.40/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.40/0.97  
% 3.40/0.97  ------ Instantiation
% 3.40/0.97  
% 3.40/0.97  inst_num_of_clauses:                    684
% 3.40/0.97  inst_num_in_passive:                    179
% 3.40/0.97  inst_num_in_active:                     405
% 3.40/0.97  inst_num_in_unprocessed:                100
% 3.40/0.97  inst_num_of_loops:                      460
% 3.40/0.97  inst_num_of_learning_restarts:          0
% 3.40/0.97  inst_num_moves_active_passive:          50
% 3.40/0.97  inst_lit_activity:                      0
% 3.40/0.97  inst_lit_activity_moves:                0
% 3.40/0.97  inst_num_tautologies:                   0
% 3.40/0.97  inst_num_prop_implied:                  0
% 3.40/0.97  inst_num_existing_simplified:           0
% 3.40/0.97  inst_num_eq_res_simplified:             0
% 3.40/0.97  inst_num_child_elim:                    0
% 3.40/0.97  inst_num_of_dismatching_blockings:      714
% 3.40/0.97  inst_num_of_non_proper_insts:           1257
% 3.40/0.97  inst_num_of_duplicates:                 0
% 3.40/0.97  inst_inst_num_from_inst_to_res:         0
% 3.40/0.97  inst_dismatching_checking_time:         0.
% 3.40/0.97  
% 3.40/0.97  ------ Resolution
% 3.40/0.97  
% 3.40/0.97  res_num_of_clauses:                     0
% 3.40/0.97  res_num_in_passive:                     0
% 3.40/0.97  res_num_in_active:                      0
% 3.40/0.97  res_num_of_loops:                       134
% 3.40/0.97  res_forward_subset_subsumed:            173
% 3.40/0.97  res_backward_subset_subsumed:           4
% 3.40/0.97  res_forward_subsumed:                   0
% 3.40/0.97  res_backward_subsumed:                  0
% 3.40/0.97  res_forward_subsumption_resolution:     1
% 3.40/0.97  res_backward_subsumption_resolution:    0
% 3.40/0.97  res_clause_to_clause_subsumption:       235
% 3.40/0.97  res_orphan_elimination:                 0
% 3.40/0.97  res_tautology_del:                      156
% 3.40/0.97  res_num_eq_res_simplified:              0
% 3.40/0.97  res_num_sel_changes:                    0
% 3.40/0.97  res_moves_from_active_to_pass:          0
% 3.40/0.97  
% 3.40/0.97  ------ Superposition
% 3.40/0.97  
% 3.40/0.97  sup_time_total:                         0.
% 3.40/0.97  sup_time_generating:                    0.
% 3.40/0.97  sup_time_sim_full:                      0.
% 3.40/0.97  sup_time_sim_immed:                     0.
% 3.40/0.97  
% 3.40/0.97  sup_num_of_clauses:                     97
% 3.40/0.97  sup_num_in_active:                      71
% 3.40/0.97  sup_num_in_passive:                     26
% 3.40/0.97  sup_num_of_loops:                       90
% 3.40/0.97  sup_fw_superposition:                   49
% 3.40/0.97  sup_bw_superposition:                   35
% 3.40/0.97  sup_immediate_simplified:               14
% 3.40/0.97  sup_given_eliminated:                   0
% 3.40/0.97  comparisons_done:                       0
% 3.40/0.97  comparisons_avoided:                    0
% 3.40/0.97  
% 3.40/0.97  ------ Simplifications
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  sim_fw_subset_subsumed:                 0
% 3.40/0.97  sim_bw_subset_subsumed:                 5
% 3.40/0.97  sim_fw_subsumed:                        1
% 3.40/0.97  sim_bw_subsumed:                        0
% 3.40/0.97  sim_fw_subsumption_res:                 2
% 3.40/0.97  sim_bw_subsumption_res:                 0
% 3.40/0.97  sim_tautology_del:                      0
% 3.40/0.97  sim_eq_tautology_del:                   3
% 3.40/0.97  sim_eq_res_simp:                        0
% 3.40/0.97  sim_fw_demodulated:                     3
% 3.40/0.97  sim_bw_demodulated:                     16
% 3.40/0.97  sim_light_normalised:                   19
% 3.40/0.97  sim_joinable_taut:                      0
% 3.40/0.97  sim_joinable_simp:                      0
% 3.40/0.97  sim_ac_normalised:                      0
% 3.40/0.97  sim_smt_subsumption:                    0
% 3.40/0.97  
%------------------------------------------------------------------------------
