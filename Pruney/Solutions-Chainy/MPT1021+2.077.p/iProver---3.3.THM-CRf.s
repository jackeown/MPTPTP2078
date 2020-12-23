%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:34 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  179 (1199 expanded)
%              Number of clauses        :  111 ( 387 expanded)
%              Number of leaves         :   16 ( 228 expanded)
%              Depth                    :   21
%              Number of atoms          :  598 (5569 expanded)
%              Number of equality atoms :  224 ( 584 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f41])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f69,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_611,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1098,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_614,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49)
    | k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1095,plain,
    ( k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49)
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2142,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1095])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_698,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_2424,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2142,c_25,c_24,c_23,c_22,c_698])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_619,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1090,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_2750,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_1090])).

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

cnf(c_4026,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2750,c_26,c_27,c_28,c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1094,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_4042,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4026,c_1094])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_616,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ v3_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1093,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2057,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1093])).

cnf(c_691,plain,
    ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_693,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_2324,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2057,c_26,c_27,c_28,c_29,c_693])).

cnf(c_2427,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2424,c_2324])).

cnf(c_5805,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4042,c_2427])).

cnf(c_5806,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_5805])).

cnf(c_5814,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_5806])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_613,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(X0_49)
    | k1_relset_1(X0_50,X0_50,X0_49) = X0_50 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1096,plain,
    ( k1_relset_1(X0_50,X0_50,X0_49) = X0_50
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2031,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1096])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1085,plain,
    ( k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1356,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1098,c_1085])).

cnf(c_2043,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2031,c_1356])).

cnf(c_2653,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2043,c_26,c_27])).

cnf(c_608,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1101,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_625,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1084,plain,
    ( k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49))
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1492,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1084])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_669,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_620,plain,
    ( ~ v3_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | v2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_680,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_relat_1(X1_49)
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_49)
    | ~ v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1295,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_1820,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1492,c_25,c_23,c_22,c_87,c_669,c_680,c_1295])).

cnf(c_2656,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_2653,c_1820])).

cnf(c_5840,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5814,c_2656])).

cnf(c_5962,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5840,c_26])).

cnf(c_3044,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1094])).

cnf(c_3147,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3044,c_26])).

cnf(c_3148,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3147])).

cnf(c_3155,plain,
    ( k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1)
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_2(X0_50,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3148])).

cnf(c_4329,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3155,c_691])).

cnf(c_4330,plain,
    ( k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1)
    | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4329])).

cnf(c_4340,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_4330])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_327,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_328,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_344,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_4])).

cnf(c_607,plain,
    ( ~ v3_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k2_relat_1(X0_49) = X1_50 ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_1102,plain,
    ( k2_relat_1(X0_49) = X0_50
    | v3_funct_2(X0_49,X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_3593,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1102])).

cnf(c_709,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_3857,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3593,c_25,c_23,c_22,c_87,c_709,c_1295])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_626,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1083,plain,
    ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1485,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1083])).

cnf(c_666,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1766,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1485,c_25,c_23,c_22,c_87,c_666,c_680,c_1295])).

cnf(c_3860,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3857,c_1766])).

cnf(c_4380,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4340,c_2424,c_3860])).

cnf(c_4031,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4026,c_3148])).

cnf(c_4137,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4031,c_3860])).

cnf(c_4534,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_2427,c_4137])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_612,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1097,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2428,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2424,c_1097])).

cnf(c_4537,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4534,c_2428])).

cnf(c_8,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_621,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1088,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_623,plain,
    ( r2_relset_1(X0_50,X1_50,X0_49,X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1086,plain,
    ( r2_relset_1(X0_50,X1_50,X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_1443,plain,
    ( r2_relset_1(X0_50,X0_50,k6_partfun1(X0_50),k6_partfun1(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1086])).

cnf(c_1450,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_4540,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4537,c_1450])).

cnf(c_5965,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5962,c_4540])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5965,c_1450])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.03/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.02  
% 2.03/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/1.02  
% 2.03/1.02  ------  iProver source info
% 2.03/1.02  
% 2.03/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.03/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/1.02  git: non_committed_changes: false
% 2.03/1.02  git: last_make_outside_of_git: false
% 2.03/1.02  
% 2.03/1.02  ------ 
% 2.03/1.02  
% 2.03/1.02  ------ Input Options
% 2.03/1.02  
% 2.03/1.02  --out_options                           all
% 2.03/1.02  --tptp_safe_out                         true
% 2.03/1.02  --problem_path                          ""
% 2.03/1.02  --include_path                          ""
% 2.03/1.02  --clausifier                            res/vclausify_rel
% 2.03/1.02  --clausifier_options                    --mode clausify
% 2.03/1.02  --stdin                                 false
% 2.03/1.02  --stats_out                             all
% 2.03/1.02  
% 2.03/1.02  ------ General Options
% 2.03/1.02  
% 2.03/1.02  --fof                                   false
% 2.03/1.02  --time_out_real                         305.
% 2.03/1.02  --time_out_virtual                      -1.
% 2.03/1.02  --symbol_type_check                     false
% 2.03/1.02  --clausify_out                          false
% 2.03/1.02  --sig_cnt_out                           false
% 2.03/1.02  --trig_cnt_out                          false
% 2.03/1.02  --trig_cnt_out_tolerance                1.
% 2.03/1.02  --trig_cnt_out_sk_spl                   false
% 2.03/1.02  --abstr_cl_out                          false
% 2.03/1.02  
% 2.03/1.02  ------ Global Options
% 2.03/1.02  
% 2.03/1.02  --schedule                              default
% 2.03/1.02  --add_important_lit                     false
% 2.03/1.02  --prop_solver_per_cl                    1000
% 2.03/1.02  --min_unsat_core                        false
% 2.03/1.02  --soft_assumptions                      false
% 2.03/1.02  --soft_lemma_size                       3
% 2.03/1.02  --prop_impl_unit_size                   0
% 2.03/1.02  --prop_impl_unit                        []
% 2.03/1.02  --share_sel_clauses                     true
% 2.03/1.02  --reset_solvers                         false
% 2.03/1.02  --bc_imp_inh                            [conj_cone]
% 2.03/1.02  --conj_cone_tolerance                   3.
% 2.03/1.02  --extra_neg_conj                        none
% 2.03/1.02  --large_theory_mode                     true
% 2.03/1.02  --prolific_symb_bound                   200
% 2.03/1.02  --lt_threshold                          2000
% 2.03/1.02  --clause_weak_htbl                      true
% 2.03/1.02  --gc_record_bc_elim                     false
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing Options
% 2.03/1.02  
% 2.03/1.02  --preprocessing_flag                    true
% 2.03/1.02  --time_out_prep_mult                    0.1
% 2.03/1.02  --splitting_mode                        input
% 2.03/1.02  --splitting_grd                         true
% 2.03/1.02  --splitting_cvd                         false
% 2.03/1.02  --splitting_cvd_svl                     false
% 2.03/1.02  --splitting_nvd                         32
% 2.03/1.02  --sub_typing                            true
% 2.03/1.02  --prep_gs_sim                           true
% 2.03/1.02  --prep_unflatten                        true
% 2.03/1.02  --prep_res_sim                          true
% 2.03/1.02  --prep_upred                            true
% 2.03/1.02  --prep_sem_filter                       exhaustive
% 2.03/1.02  --prep_sem_filter_out                   false
% 2.03/1.02  --pred_elim                             true
% 2.03/1.02  --res_sim_input                         true
% 2.03/1.02  --eq_ax_congr_red                       true
% 2.03/1.02  --pure_diseq_elim                       true
% 2.03/1.02  --brand_transform                       false
% 2.03/1.02  --non_eq_to_eq                          false
% 2.03/1.02  --prep_def_merge                        true
% 2.03/1.02  --prep_def_merge_prop_impl              false
% 2.03/1.02  --prep_def_merge_mbd                    true
% 2.03/1.02  --prep_def_merge_tr_red                 false
% 2.03/1.02  --prep_def_merge_tr_cl                  false
% 2.03/1.02  --smt_preprocessing                     true
% 2.03/1.02  --smt_ac_axioms                         fast
% 2.03/1.02  --preprocessed_out                      false
% 2.03/1.02  --preprocessed_stats                    false
% 2.03/1.02  
% 2.03/1.02  ------ Abstraction refinement Options
% 2.03/1.02  
% 2.03/1.02  --abstr_ref                             []
% 2.03/1.02  --abstr_ref_prep                        false
% 2.03/1.02  --abstr_ref_until_sat                   false
% 2.03/1.02  --abstr_ref_sig_restrict                funpre
% 2.03/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/1.02  --abstr_ref_under                       []
% 2.03/1.02  
% 2.03/1.02  ------ SAT Options
% 2.03/1.02  
% 2.03/1.02  --sat_mode                              false
% 2.03/1.02  --sat_fm_restart_options                ""
% 2.03/1.02  --sat_gr_def                            false
% 2.03/1.02  --sat_epr_types                         true
% 2.03/1.02  --sat_non_cyclic_types                  false
% 2.03/1.02  --sat_finite_models                     false
% 2.03/1.02  --sat_fm_lemmas                         false
% 2.03/1.02  --sat_fm_prep                           false
% 2.03/1.02  --sat_fm_uc_incr                        true
% 2.03/1.02  --sat_out_model                         small
% 2.03/1.02  --sat_out_clauses                       false
% 2.03/1.02  
% 2.03/1.02  ------ QBF Options
% 2.03/1.02  
% 2.03/1.02  --qbf_mode                              false
% 2.03/1.02  --qbf_elim_univ                         false
% 2.03/1.02  --qbf_dom_inst                          none
% 2.03/1.02  --qbf_dom_pre_inst                      false
% 2.03/1.02  --qbf_sk_in                             false
% 2.03/1.02  --qbf_pred_elim                         true
% 2.03/1.02  --qbf_split                             512
% 2.03/1.02  
% 2.03/1.02  ------ BMC1 Options
% 2.03/1.02  
% 2.03/1.02  --bmc1_incremental                      false
% 2.03/1.02  --bmc1_axioms                           reachable_all
% 2.03/1.02  --bmc1_min_bound                        0
% 2.03/1.02  --bmc1_max_bound                        -1
% 2.03/1.02  --bmc1_max_bound_default                -1
% 2.03/1.02  --bmc1_symbol_reachability              true
% 2.03/1.02  --bmc1_property_lemmas                  false
% 2.03/1.02  --bmc1_k_induction                      false
% 2.03/1.02  --bmc1_non_equiv_states                 false
% 2.03/1.02  --bmc1_deadlock                         false
% 2.03/1.02  --bmc1_ucm                              false
% 2.03/1.02  --bmc1_add_unsat_core                   none
% 2.03/1.02  --bmc1_unsat_core_children              false
% 2.03/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/1.02  --bmc1_out_stat                         full
% 2.03/1.02  --bmc1_ground_init                      false
% 2.03/1.02  --bmc1_pre_inst_next_state              false
% 2.03/1.02  --bmc1_pre_inst_state                   false
% 2.03/1.02  --bmc1_pre_inst_reach_state             false
% 2.03/1.02  --bmc1_out_unsat_core                   false
% 2.03/1.02  --bmc1_aig_witness_out                  false
% 2.03/1.02  --bmc1_verbose                          false
% 2.03/1.02  --bmc1_dump_clauses_tptp                false
% 2.03/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.03/1.02  --bmc1_dump_file                        -
% 2.03/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.03/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.03/1.02  --bmc1_ucm_extend_mode                  1
% 2.03/1.02  --bmc1_ucm_init_mode                    2
% 2.03/1.02  --bmc1_ucm_cone_mode                    none
% 2.03/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.03/1.02  --bmc1_ucm_relax_model                  4
% 2.03/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.03/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/1.02  --bmc1_ucm_layered_model                none
% 2.03/1.02  --bmc1_ucm_max_lemma_size               10
% 2.03/1.02  
% 2.03/1.02  ------ AIG Options
% 2.03/1.02  
% 2.03/1.02  --aig_mode                              false
% 2.03/1.02  
% 2.03/1.02  ------ Instantiation Options
% 2.03/1.02  
% 2.03/1.02  --instantiation_flag                    true
% 2.03/1.02  --inst_sos_flag                         false
% 2.03/1.02  --inst_sos_phase                        true
% 2.03/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel_side                     num_symb
% 2.03/1.02  --inst_solver_per_active                1400
% 2.03/1.02  --inst_solver_calls_frac                1.
% 2.03/1.02  --inst_passive_queue_type               priority_queues
% 2.03/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/1.02  --inst_passive_queues_freq              [25;2]
% 2.03/1.02  --inst_dismatching                      true
% 2.03/1.02  --inst_eager_unprocessed_to_passive     true
% 2.03/1.02  --inst_prop_sim_given                   true
% 2.03/1.02  --inst_prop_sim_new                     false
% 2.03/1.02  --inst_subs_new                         false
% 2.03/1.02  --inst_eq_res_simp                      false
% 2.03/1.02  --inst_subs_given                       false
% 2.03/1.02  --inst_orphan_elimination               true
% 2.03/1.02  --inst_learning_loop_flag               true
% 2.03/1.02  --inst_learning_start                   3000
% 2.03/1.02  --inst_learning_factor                  2
% 2.03/1.02  --inst_start_prop_sim_after_learn       3
% 2.03/1.02  --inst_sel_renew                        solver
% 2.03/1.02  --inst_lit_activity_flag                true
% 2.03/1.02  --inst_restr_to_given                   false
% 2.03/1.02  --inst_activity_threshold               500
% 2.03/1.02  --inst_out_proof                        true
% 2.03/1.02  
% 2.03/1.02  ------ Resolution Options
% 2.03/1.02  
% 2.03/1.02  --resolution_flag                       true
% 2.03/1.02  --res_lit_sel                           adaptive
% 2.03/1.02  --res_lit_sel_side                      none
% 2.03/1.02  --res_ordering                          kbo
% 2.03/1.02  --res_to_prop_solver                    active
% 2.03/1.02  --res_prop_simpl_new                    false
% 2.03/1.02  --res_prop_simpl_given                  true
% 2.03/1.02  --res_passive_queue_type                priority_queues
% 2.03/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/1.03  --res_passive_queues_freq               [15;5]
% 2.03/1.03  --res_forward_subs                      full
% 2.03/1.03  --res_backward_subs                     full
% 2.03/1.03  --res_forward_subs_resolution           true
% 2.03/1.03  --res_backward_subs_resolution          true
% 2.03/1.03  --res_orphan_elimination                true
% 2.03/1.03  --res_time_limit                        2.
% 2.03/1.03  --res_out_proof                         true
% 2.03/1.03  
% 2.03/1.03  ------ Superposition Options
% 2.03/1.03  
% 2.03/1.03  --superposition_flag                    true
% 2.03/1.03  --sup_passive_queue_type                priority_queues
% 2.03/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.03/1.03  --demod_completeness_check              fast
% 2.03/1.03  --demod_use_ground                      true
% 2.03/1.03  --sup_to_prop_solver                    passive
% 2.03/1.03  --sup_prop_simpl_new                    true
% 2.03/1.03  --sup_prop_simpl_given                  true
% 2.03/1.03  --sup_fun_splitting                     false
% 2.03/1.03  --sup_smt_interval                      50000
% 2.03/1.03  
% 2.03/1.03  ------ Superposition Simplification Setup
% 2.03/1.03  
% 2.03/1.03  --sup_indices_passive                   []
% 2.03/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_full_bw                           [BwDemod]
% 2.03/1.03  --sup_immed_triv                        [TrivRules]
% 2.03/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_immed_bw_main                     []
% 2.03/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.03  
% 2.03/1.03  ------ Combination Options
% 2.03/1.03  
% 2.03/1.03  --comb_res_mult                         3
% 2.03/1.03  --comb_sup_mult                         2
% 2.03/1.03  --comb_inst_mult                        10
% 2.03/1.03  
% 2.03/1.03  ------ Debug Options
% 2.03/1.03  
% 2.03/1.03  --dbg_backtrace                         false
% 2.03/1.03  --dbg_dump_prop_clauses                 false
% 2.03/1.03  --dbg_dump_prop_clauses_file            -
% 2.03/1.03  --dbg_out_stat                          false
% 2.03/1.03  ------ Parsing...
% 2.03/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/1.03  
% 2.03/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.03/1.03  
% 2.03/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/1.03  
% 2.03/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/1.03  ------ Proving...
% 2.03/1.03  ------ Problem Properties 
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  clauses                                 22
% 2.03/1.03  conjectures                             5
% 2.03/1.03  EPR                                     3
% 2.03/1.03  Horn                                    22
% 2.03/1.03  unary                                   6
% 2.03/1.03  binary                                  3
% 2.03/1.03  lits                                    70
% 2.03/1.03  lits eq                                 8
% 2.03/1.03  fd_pure                                 0
% 2.03/1.03  fd_pseudo                               0
% 2.03/1.03  fd_cond                                 0
% 2.03/1.03  fd_pseudo_cond                          2
% 2.03/1.03  AC symbols                              0
% 2.03/1.03  
% 2.03/1.03  ------ Schedule dynamic 5 is on 
% 2.03/1.03  
% 2.03/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  ------ 
% 2.03/1.03  Current options:
% 2.03/1.03  ------ 
% 2.03/1.03  
% 2.03/1.03  ------ Input Options
% 2.03/1.03  
% 2.03/1.03  --out_options                           all
% 2.03/1.03  --tptp_safe_out                         true
% 2.03/1.03  --problem_path                          ""
% 2.03/1.03  --include_path                          ""
% 2.03/1.03  --clausifier                            res/vclausify_rel
% 2.03/1.03  --clausifier_options                    --mode clausify
% 2.03/1.03  --stdin                                 false
% 2.03/1.03  --stats_out                             all
% 2.03/1.03  
% 2.03/1.03  ------ General Options
% 2.03/1.03  
% 2.03/1.03  --fof                                   false
% 2.03/1.03  --time_out_real                         305.
% 2.03/1.03  --time_out_virtual                      -1.
% 2.03/1.03  --symbol_type_check                     false
% 2.03/1.03  --clausify_out                          false
% 2.03/1.03  --sig_cnt_out                           false
% 2.03/1.03  --trig_cnt_out                          false
% 2.03/1.03  --trig_cnt_out_tolerance                1.
% 2.03/1.03  --trig_cnt_out_sk_spl                   false
% 2.03/1.03  --abstr_cl_out                          false
% 2.03/1.03  
% 2.03/1.03  ------ Global Options
% 2.03/1.03  
% 2.03/1.03  --schedule                              default
% 2.03/1.03  --add_important_lit                     false
% 2.03/1.03  --prop_solver_per_cl                    1000
% 2.03/1.03  --min_unsat_core                        false
% 2.03/1.03  --soft_assumptions                      false
% 2.03/1.03  --soft_lemma_size                       3
% 2.03/1.03  --prop_impl_unit_size                   0
% 2.03/1.03  --prop_impl_unit                        []
% 2.03/1.03  --share_sel_clauses                     true
% 2.03/1.03  --reset_solvers                         false
% 2.03/1.03  --bc_imp_inh                            [conj_cone]
% 2.03/1.03  --conj_cone_tolerance                   3.
% 2.03/1.03  --extra_neg_conj                        none
% 2.03/1.03  --large_theory_mode                     true
% 2.03/1.03  --prolific_symb_bound                   200
% 2.03/1.03  --lt_threshold                          2000
% 2.03/1.03  --clause_weak_htbl                      true
% 2.03/1.03  --gc_record_bc_elim                     false
% 2.03/1.03  
% 2.03/1.03  ------ Preprocessing Options
% 2.03/1.03  
% 2.03/1.03  --preprocessing_flag                    true
% 2.03/1.03  --time_out_prep_mult                    0.1
% 2.03/1.03  --splitting_mode                        input
% 2.03/1.03  --splitting_grd                         true
% 2.03/1.03  --splitting_cvd                         false
% 2.03/1.03  --splitting_cvd_svl                     false
% 2.03/1.03  --splitting_nvd                         32
% 2.03/1.03  --sub_typing                            true
% 2.03/1.03  --prep_gs_sim                           true
% 2.03/1.03  --prep_unflatten                        true
% 2.03/1.03  --prep_res_sim                          true
% 2.03/1.03  --prep_upred                            true
% 2.03/1.03  --prep_sem_filter                       exhaustive
% 2.03/1.03  --prep_sem_filter_out                   false
% 2.03/1.03  --pred_elim                             true
% 2.03/1.03  --res_sim_input                         true
% 2.03/1.03  --eq_ax_congr_red                       true
% 2.03/1.03  --pure_diseq_elim                       true
% 2.03/1.03  --brand_transform                       false
% 2.03/1.03  --non_eq_to_eq                          false
% 2.03/1.03  --prep_def_merge                        true
% 2.03/1.03  --prep_def_merge_prop_impl              false
% 2.03/1.03  --prep_def_merge_mbd                    true
% 2.03/1.03  --prep_def_merge_tr_red                 false
% 2.03/1.03  --prep_def_merge_tr_cl                  false
% 2.03/1.03  --smt_preprocessing                     true
% 2.03/1.03  --smt_ac_axioms                         fast
% 2.03/1.03  --preprocessed_out                      false
% 2.03/1.03  --preprocessed_stats                    false
% 2.03/1.03  
% 2.03/1.03  ------ Abstraction refinement Options
% 2.03/1.03  
% 2.03/1.03  --abstr_ref                             []
% 2.03/1.03  --abstr_ref_prep                        false
% 2.03/1.03  --abstr_ref_until_sat                   false
% 2.03/1.03  --abstr_ref_sig_restrict                funpre
% 2.03/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/1.03  --abstr_ref_under                       []
% 2.03/1.03  
% 2.03/1.03  ------ SAT Options
% 2.03/1.03  
% 2.03/1.03  --sat_mode                              false
% 2.03/1.03  --sat_fm_restart_options                ""
% 2.03/1.03  --sat_gr_def                            false
% 2.03/1.03  --sat_epr_types                         true
% 2.03/1.03  --sat_non_cyclic_types                  false
% 2.03/1.03  --sat_finite_models                     false
% 2.03/1.03  --sat_fm_lemmas                         false
% 2.03/1.03  --sat_fm_prep                           false
% 2.03/1.03  --sat_fm_uc_incr                        true
% 2.03/1.03  --sat_out_model                         small
% 2.03/1.03  --sat_out_clauses                       false
% 2.03/1.03  
% 2.03/1.03  ------ QBF Options
% 2.03/1.03  
% 2.03/1.03  --qbf_mode                              false
% 2.03/1.03  --qbf_elim_univ                         false
% 2.03/1.03  --qbf_dom_inst                          none
% 2.03/1.03  --qbf_dom_pre_inst                      false
% 2.03/1.03  --qbf_sk_in                             false
% 2.03/1.03  --qbf_pred_elim                         true
% 2.03/1.03  --qbf_split                             512
% 2.03/1.03  
% 2.03/1.03  ------ BMC1 Options
% 2.03/1.03  
% 2.03/1.03  --bmc1_incremental                      false
% 2.03/1.03  --bmc1_axioms                           reachable_all
% 2.03/1.03  --bmc1_min_bound                        0
% 2.03/1.03  --bmc1_max_bound                        -1
% 2.03/1.03  --bmc1_max_bound_default                -1
% 2.03/1.03  --bmc1_symbol_reachability              true
% 2.03/1.03  --bmc1_property_lemmas                  false
% 2.03/1.03  --bmc1_k_induction                      false
% 2.03/1.03  --bmc1_non_equiv_states                 false
% 2.03/1.03  --bmc1_deadlock                         false
% 2.03/1.03  --bmc1_ucm                              false
% 2.03/1.03  --bmc1_add_unsat_core                   none
% 2.03/1.03  --bmc1_unsat_core_children              false
% 2.03/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/1.03  --bmc1_out_stat                         full
% 2.03/1.03  --bmc1_ground_init                      false
% 2.03/1.03  --bmc1_pre_inst_next_state              false
% 2.03/1.03  --bmc1_pre_inst_state                   false
% 2.03/1.03  --bmc1_pre_inst_reach_state             false
% 2.03/1.03  --bmc1_out_unsat_core                   false
% 2.03/1.03  --bmc1_aig_witness_out                  false
% 2.03/1.03  --bmc1_verbose                          false
% 2.03/1.03  --bmc1_dump_clauses_tptp                false
% 2.03/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.03/1.03  --bmc1_dump_file                        -
% 2.03/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.03/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.03/1.03  --bmc1_ucm_extend_mode                  1
% 2.03/1.03  --bmc1_ucm_init_mode                    2
% 2.03/1.03  --bmc1_ucm_cone_mode                    none
% 2.03/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.03/1.03  --bmc1_ucm_relax_model                  4
% 2.03/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.03/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/1.03  --bmc1_ucm_layered_model                none
% 2.03/1.03  --bmc1_ucm_max_lemma_size               10
% 2.03/1.03  
% 2.03/1.03  ------ AIG Options
% 2.03/1.03  
% 2.03/1.03  --aig_mode                              false
% 2.03/1.03  
% 2.03/1.03  ------ Instantiation Options
% 2.03/1.03  
% 2.03/1.03  --instantiation_flag                    true
% 2.03/1.03  --inst_sos_flag                         false
% 2.03/1.03  --inst_sos_phase                        true
% 2.03/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/1.03  --inst_lit_sel_side                     none
% 2.03/1.03  --inst_solver_per_active                1400
% 2.03/1.03  --inst_solver_calls_frac                1.
% 2.03/1.03  --inst_passive_queue_type               priority_queues
% 2.03/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/1.03  --inst_passive_queues_freq              [25;2]
% 2.03/1.03  --inst_dismatching                      true
% 2.03/1.03  --inst_eager_unprocessed_to_passive     true
% 2.03/1.03  --inst_prop_sim_given                   true
% 2.03/1.03  --inst_prop_sim_new                     false
% 2.03/1.03  --inst_subs_new                         false
% 2.03/1.03  --inst_eq_res_simp                      false
% 2.03/1.03  --inst_subs_given                       false
% 2.03/1.03  --inst_orphan_elimination               true
% 2.03/1.03  --inst_learning_loop_flag               true
% 2.03/1.03  --inst_learning_start                   3000
% 2.03/1.03  --inst_learning_factor                  2
% 2.03/1.03  --inst_start_prop_sim_after_learn       3
% 2.03/1.03  --inst_sel_renew                        solver
% 2.03/1.03  --inst_lit_activity_flag                true
% 2.03/1.03  --inst_restr_to_given                   false
% 2.03/1.03  --inst_activity_threshold               500
% 2.03/1.03  --inst_out_proof                        true
% 2.03/1.03  
% 2.03/1.03  ------ Resolution Options
% 2.03/1.03  
% 2.03/1.03  --resolution_flag                       false
% 2.03/1.03  --res_lit_sel                           adaptive
% 2.03/1.03  --res_lit_sel_side                      none
% 2.03/1.03  --res_ordering                          kbo
% 2.03/1.03  --res_to_prop_solver                    active
% 2.03/1.03  --res_prop_simpl_new                    false
% 2.03/1.03  --res_prop_simpl_given                  true
% 2.03/1.03  --res_passive_queue_type                priority_queues
% 2.03/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/1.03  --res_passive_queues_freq               [15;5]
% 2.03/1.03  --res_forward_subs                      full
% 2.03/1.03  --res_backward_subs                     full
% 2.03/1.03  --res_forward_subs_resolution           true
% 2.03/1.03  --res_backward_subs_resolution          true
% 2.03/1.03  --res_orphan_elimination                true
% 2.03/1.03  --res_time_limit                        2.
% 2.03/1.03  --res_out_proof                         true
% 2.03/1.03  
% 2.03/1.03  ------ Superposition Options
% 2.03/1.03  
% 2.03/1.03  --superposition_flag                    true
% 2.03/1.03  --sup_passive_queue_type                priority_queues
% 2.03/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.03/1.03  --demod_completeness_check              fast
% 2.03/1.03  --demod_use_ground                      true
% 2.03/1.03  --sup_to_prop_solver                    passive
% 2.03/1.03  --sup_prop_simpl_new                    true
% 2.03/1.03  --sup_prop_simpl_given                  true
% 2.03/1.03  --sup_fun_splitting                     false
% 2.03/1.03  --sup_smt_interval                      50000
% 2.03/1.03  
% 2.03/1.03  ------ Superposition Simplification Setup
% 2.03/1.03  
% 2.03/1.03  --sup_indices_passive                   []
% 2.03/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_full_bw                           [BwDemod]
% 2.03/1.03  --sup_immed_triv                        [TrivRules]
% 2.03/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_immed_bw_main                     []
% 2.03/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.03  
% 2.03/1.03  ------ Combination Options
% 2.03/1.03  
% 2.03/1.03  --comb_res_mult                         3
% 2.03/1.03  --comb_sup_mult                         2
% 2.03/1.03  --comb_inst_mult                        10
% 2.03/1.03  
% 2.03/1.03  ------ Debug Options
% 2.03/1.03  
% 2.03/1.03  --dbg_backtrace                         false
% 2.03/1.03  --dbg_dump_prop_clauses                 false
% 2.03/1.03  --dbg_dump_prop_clauses_file            -
% 2.03/1.03  --dbg_out_stat                          false
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  ------ Proving...
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  % SZS status Theorem for theBenchmark.p
% 2.03/1.03  
% 2.03/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/1.03  
% 2.03/1.03  fof(f15,conjecture,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f16,negated_conjecture,(
% 2.03/1.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.03/1.03    inference(negated_conjecture,[],[f15])).
% 2.03/1.03  
% 2.03/1.03  fof(f37,plain,(
% 2.03/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.03/1.03    inference(ennf_transformation,[],[f16])).
% 2.03/1.03  
% 2.03/1.03  fof(f38,plain,(
% 2.03/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.03/1.03    inference(flattening,[],[f37])).
% 2.03/1.03  
% 2.03/1.03  fof(f41,plain,(
% 2.03/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.03/1.03    introduced(choice_axiom,[])).
% 2.03/1.03  
% 2.03/1.03  fof(f42,plain,(
% 2.03/1.03    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.03/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f41])).
% 2.03/1.03  
% 2.03/1.03  fof(f68,plain,(
% 2.03/1.03    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/1.03    inference(cnf_transformation,[],[f42])).
% 2.03/1.03  
% 2.03/1.03  fof(f12,axiom,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f33,plain,(
% 2.03/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.03/1.03    inference(ennf_transformation,[],[f12])).
% 2.03/1.03  
% 2.03/1.03  fof(f34,plain,(
% 2.03/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.03/1.03    inference(flattening,[],[f33])).
% 2.03/1.03  
% 2.03/1.03  fof(f62,plain,(
% 2.03/1.03    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f34])).
% 2.03/1.03  
% 2.03/1.03  fof(f65,plain,(
% 2.03/1.03    v1_funct_1(sK1)),
% 2.03/1.03    inference(cnf_transformation,[],[f42])).
% 2.03/1.03  
% 2.03/1.03  fof(f66,plain,(
% 2.03/1.03    v1_funct_2(sK1,sK0,sK0)),
% 2.03/1.03    inference(cnf_transformation,[],[f42])).
% 2.03/1.03  
% 2.03/1.03  fof(f67,plain,(
% 2.03/1.03    v3_funct_2(sK1,sK0,sK0)),
% 2.03/1.03    inference(cnf_transformation,[],[f42])).
% 2.03/1.03  
% 2.03/1.03  fof(f10,axiom,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f29,plain,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.03/1.03    inference(ennf_transformation,[],[f10])).
% 2.03/1.03  
% 2.03/1.03  fof(f30,plain,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.03/1.03    inference(flattening,[],[f29])).
% 2.03/1.03  
% 2.03/1.03  fof(f60,plain,(
% 2.03/1.03    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f30])).
% 2.03/1.03  
% 2.03/1.03  fof(f11,axiom,(
% 2.03/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f31,plain,(
% 2.03/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/1.03    inference(ennf_transformation,[],[f11])).
% 2.03/1.03  
% 2.03/1.03  fof(f32,plain,(
% 2.03/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/1.03    inference(flattening,[],[f31])).
% 2.03/1.03  
% 2.03/1.03  fof(f61,plain,(
% 2.03/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f32])).
% 2.03/1.03  
% 2.03/1.03  fof(f57,plain,(
% 2.03/1.03    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f30])).
% 2.03/1.03  
% 2.03/1.03  fof(f14,axiom,(
% 2.03/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f35,plain,(
% 2.03/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.03/1.03    inference(ennf_transformation,[],[f14])).
% 2.03/1.03  
% 2.03/1.03  fof(f36,plain,(
% 2.03/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.03/1.03    inference(flattening,[],[f35])).
% 2.03/1.03  
% 2.03/1.03  fof(f64,plain,(
% 2.03/1.03    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f36])).
% 2.03/1.03  
% 2.03/1.03  fof(f5,axiom,(
% 2.03/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f22,plain,(
% 2.03/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(ennf_transformation,[],[f5])).
% 2.03/1.03  
% 2.03/1.03  fof(f48,plain,(
% 2.03/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f22])).
% 2.03/1.03  
% 2.03/1.03  fof(f3,axiom,(
% 2.03/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f19,plain,(
% 2.03/1.03    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/1.03    inference(ennf_transformation,[],[f3])).
% 2.03/1.03  
% 2.03/1.03  fof(f20,plain,(
% 2.03/1.03    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/1.03    inference(flattening,[],[f19])).
% 2.03/1.03  
% 2.03/1.03  fof(f45,plain,(
% 2.03/1.03    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f20])).
% 2.03/1.03  
% 2.03/1.03  fof(f13,axiom,(
% 2.03/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f63,plain,(
% 2.03/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f13])).
% 2.03/1.03  
% 2.03/1.03  fof(f71,plain,(
% 2.03/1.03    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/1.03    inference(definition_unfolding,[],[f45,f63])).
% 2.03/1.03  
% 2.03/1.03  fof(f2,axiom,(
% 2.03/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f44,plain,(
% 2.03/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f2])).
% 2.03/1.03  
% 2.03/1.03  fof(f8,axiom,(
% 2.03/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f25,plain,(
% 2.03/1.03    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(ennf_transformation,[],[f8])).
% 2.03/1.03  
% 2.03/1.03  fof(f26,plain,(
% 2.03/1.03    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(flattening,[],[f25])).
% 2.03/1.03  
% 2.03/1.03  fof(f53,plain,(
% 2.03/1.03    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f26])).
% 2.03/1.03  
% 2.03/1.03  fof(f1,axiom,(
% 2.03/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f18,plain,(
% 2.03/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.03/1.03    inference(ennf_transformation,[],[f1])).
% 2.03/1.03  
% 2.03/1.03  fof(f43,plain,(
% 2.03/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f18])).
% 2.03/1.03  
% 2.03/1.03  fof(f54,plain,(
% 2.03/1.03    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f26])).
% 2.03/1.03  
% 2.03/1.03  fof(f9,axiom,(
% 2.03/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f27,plain,(
% 2.03/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.03/1.03    inference(ennf_transformation,[],[f9])).
% 2.03/1.03  
% 2.03/1.03  fof(f28,plain,(
% 2.03/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.03/1.03    inference(flattening,[],[f27])).
% 2.03/1.03  
% 2.03/1.03  fof(f40,plain,(
% 2.03/1.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.03/1.03    inference(nnf_transformation,[],[f28])).
% 2.03/1.03  
% 2.03/1.03  fof(f55,plain,(
% 2.03/1.03    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f40])).
% 2.03/1.03  
% 2.03/1.03  fof(f4,axiom,(
% 2.03/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f17,plain,(
% 2.03/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.03/1.03    inference(pure_predicate_removal,[],[f4])).
% 2.03/1.03  
% 2.03/1.03  fof(f21,plain,(
% 2.03/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(ennf_transformation,[],[f17])).
% 2.03/1.03  
% 2.03/1.03  fof(f47,plain,(
% 2.03/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f21])).
% 2.03/1.03  
% 2.03/1.03  fof(f46,plain,(
% 2.03/1.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/1.03    inference(cnf_transformation,[],[f20])).
% 2.03/1.03  
% 2.03/1.03  fof(f70,plain,(
% 2.03/1.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/1.03    inference(definition_unfolding,[],[f46,f63])).
% 2.03/1.03  
% 2.03/1.03  fof(f69,plain,(
% 2.03/1.03    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.03/1.03    inference(cnf_transformation,[],[f42])).
% 2.03/1.03  
% 2.03/1.03  fof(f7,axiom,(
% 2.03/1.03    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f51,plain,(
% 2.03/1.03    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f7])).
% 2.03/1.03  
% 2.03/1.03  fof(f72,plain,(
% 2.03/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/1.03    inference(definition_unfolding,[],[f51,f63])).
% 2.03/1.03  
% 2.03/1.03  fof(f6,axiom,(
% 2.03/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.03  
% 2.03/1.03  fof(f23,plain,(
% 2.03/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.03/1.03    inference(ennf_transformation,[],[f6])).
% 2.03/1.03  
% 2.03/1.03  fof(f24,plain,(
% 2.03/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(flattening,[],[f23])).
% 2.03/1.03  
% 2.03/1.03  fof(f39,plain,(
% 2.03/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/1.03    inference(nnf_transformation,[],[f24])).
% 2.03/1.03  
% 2.03/1.03  fof(f50,plain,(
% 2.03/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(cnf_transformation,[],[f39])).
% 2.03/1.03  
% 2.03/1.03  fof(f73,plain,(
% 2.03/1.03    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/1.03    inference(equality_resolution,[],[f50])).
% 2.03/1.03  
% 2.03/1.03  cnf(c_22,negated_conjecture,
% 2.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.03/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_611,negated_conjecture,
% 2.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1098,plain,
% 2.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_19,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ v3_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_614,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_19]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1095,plain,
% 2.03/1.03      ( k2_funct_2(X0_50,X0_49) = k2_funct_1(X0_49)
% 2.03/1.03      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2142,plain,
% 2.03/1.03      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 2.03/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1095]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_25,negated_conjecture,
% 2.03/1.03      ( v1_funct_1(sK1) ),
% 2.03/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_24,negated_conjecture,
% 2.03/1.03      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_23,negated_conjecture,
% 2.03/1.03      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_698,plain,
% 2.03/1.03      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.03/1.03      | ~ v3_funct_2(sK1,sK0,sK0)
% 2.03/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.03/1.03      | ~ v1_funct_1(sK1)
% 2.03/1.03      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_614]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2424,plain,
% 2.03/1.03      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_2142,c_25,c_24,c_23,c_22,c_698]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_14,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ v3_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.03/1.03      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.03/1.03      | ~ v1_funct_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_619,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 2.03/1.03      | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1090,plain,
% 2.03/1.03      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | m1_subset_1(k2_funct_2(X0_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2750,plain,
% 2.03/1.03      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.03/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_2424,c_1090]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_26,plain,
% 2.03/1.03      ( v1_funct_1(sK1) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_27,plain,
% 2.03/1.03      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_28,plain,
% 2.03/1.03      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_29,plain,
% 2.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4026,plain,
% 2.03/1.03      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_2750,c_26,c_27,c_28,c_29]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_18,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v1_funct_1(X3)
% 2.03/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_615,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.03/1.03      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | ~ v1_funct_1(X1_49)
% 2.03/1.03      | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1094,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(X1_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4042,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_4026,c_1094]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_17,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ v3_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.03/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_616,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ v3_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | v1_funct_1(k2_funct_2(X0_50,X0_49)) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1093,plain,
% 2.03/1.03      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2057,plain,
% 2.03/1.03      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1093]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_691,plain,
% 2.03/1.03      ( v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_2(X0_50,X0_49)) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_693,plain,
% 2.03/1.03      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_691]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2324,plain,
% 2.03/1.03      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_2057,c_26,c_27,c_28,c_29,c_693]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2427,plain,
% 2.03/1.03      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_2424,c_2324]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5805,plain,
% 2.03/1.03      ( v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1)) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_4042,c_2427]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5806,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(renaming,[status(thm)],[c_5805]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5814,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_5806]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_20,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.03/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_613,plain,
% 2.03/1.03      ( ~ v1_funct_2(X0_49,X0_50,X0_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | k1_relset_1(X0_50,X0_50,X0_49) = X0_50 ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1096,plain,
% 2.03/1.03      ( k1_relset_1(X0_50,X0_50,X0_49) = X0_50
% 2.03/1.03      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2031,plain,
% 2.03/1.03      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 2.03/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1096]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_624,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.03/1.03      | k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1085,plain,
% 2.03/1.03      ( k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49)
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1356,plain,
% 2.03/1.03      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1085]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2043,plain,
% 2.03/1.03      ( k1_relat_1(sK1) = sK0
% 2.03/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_2031,c_1356]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2653,plain,
% 2.03/1.03      ( k1_relat_1(sK1) = sK0 ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_2043,c_26,c_27]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_608,negated_conjecture,
% 2.03/1.03      ( v1_funct_1(sK1) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1101,plain,
% 2.03/1.03      ( v1_funct_1(sK1) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3,plain,
% 2.03/1.03      ( ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v2_funct_1(X0)
% 2.03/1.03      | ~ v1_relat_1(X0)
% 2.03/1.03      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.03/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_625,plain,
% 2.03/1.03      ( ~ v1_funct_1(X0_49)
% 2.03/1.03      | ~ v2_funct_1(X0_49)
% 2.03/1.03      | ~ v1_relat_1(X0_49)
% 2.03/1.03      | k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49)) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1084,plain,
% 2.03/1.03      ( k5_relat_1(X0_49,k2_funct_1(X0_49)) = k6_partfun1(k1_relat_1(X0_49))
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v2_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_relat_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1492,plain,
% 2.03/1.03      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 2.03/1.03      | v2_funct_1(sK1) != iProver_top
% 2.03/1.03      | v1_relat_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1101,c_1084]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1,plain,
% 2.03/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.03/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_87,plain,
% 2.03/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_669,plain,
% 2.03/1.03      ( ~ v1_funct_1(sK1)
% 2.03/1.03      | ~ v2_funct_1(sK1)
% 2.03/1.03      | ~ v1_relat_1(sK1)
% 2.03/1.03      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_625]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_10,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | v2_funct_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_620,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0_49,X0_50,X1_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | v2_funct_1(X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_680,plain,
% 2.03/1.03      ( ~ v3_funct_2(sK1,sK0,sK0)
% 2.03/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.03/1.03      | ~ v1_funct_1(sK1)
% 2.03/1.03      | v2_funct_1(sK1) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_620]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_0,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.03/1.03      | ~ v1_relat_1(X1)
% 2.03/1.03      | v1_relat_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_628,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.03/1.03      | ~ v1_relat_1(X1_49)
% 2.03/1.03      | v1_relat_1(X0_49) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1293,plain,
% 2.03/1.03      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.03/1.03      | v1_relat_1(X0_49)
% 2.03/1.03      | ~ v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_628]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1295,plain,
% 2.03/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.03/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.03/1.03      | v1_relat_1(sK1) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_1293]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1820,plain,
% 2.03/1.03      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_1492,c_25,c_23,c_22,c_87,c_669,c_680,c_1295]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2656,plain,
% 2.03/1.03      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_2653,c_1820]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5840,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(light_normalisation,[status(thm)],[c_5814,c_2656]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5962,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_5840,c_26]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3044,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1094]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3147,plain,
% 2.03/1.03      ( v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_3044,c_26]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3148,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(renaming,[status(thm)],[c_3147]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3155,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1)
% 2.03/1.03      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_funct_1(k2_funct_2(X0_50,X0_49)) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1090,c_3148]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4329,plain,
% 2.03/1.03      ( v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_3155,c_691]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4330,plain,
% 2.03/1.03      ( k1_partfun1(X0_50,X0_50,sK0,sK0,k2_funct_2(X0_50,X0_49),sK1) = k5_relat_1(k2_funct_2(X0_50,X0_49),sK1)
% 2.03/1.03      | v1_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | v3_funct_2(X0_49,X0_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(renaming,[status(thm)],[c_4329]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4340,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 2.03/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_4330]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_9,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 2.03/1.03      | v2_funct_2(X0,X2)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ v1_funct_1(X0) ),
% 2.03/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_13,plain,
% 2.03/1.03      ( ~ v2_funct_2(X0,X1)
% 2.03/1.03      | ~ v5_relat_1(X0,X1)
% 2.03/1.03      | ~ v1_relat_1(X0)
% 2.03/1.03      | k2_relat_1(X0) = X1 ),
% 2.03/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_327,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 2.03/1.03      | ~ v5_relat_1(X3,X4)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v1_relat_1(X3)
% 2.03/1.03      | X3 != X0
% 2.03/1.03      | X4 != X2
% 2.03/1.03      | k2_relat_1(X3) = X4 ),
% 2.03/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_328,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 2.03/1.03      | ~ v5_relat_1(X0,X2)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v1_relat_1(X0)
% 2.03/1.03      | k2_relat_1(X0) = X2 ),
% 2.03/1.03      inference(unflattening,[status(thm)],[c_327]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4,plain,
% 2.03/1.03      ( v5_relat_1(X0,X1)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.03/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_344,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 2.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.03      | ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v1_relat_1(X0)
% 2.03/1.03      | k2_relat_1(X0) = X2 ),
% 2.03/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_328,c_4]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_607,plain,
% 2.03/1.03      ( ~ v3_funct_2(X0_49,X0_50,X1_50)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.03/1.03      | ~ v1_funct_1(X0_49)
% 2.03/1.03      | ~ v1_relat_1(X0_49)
% 2.03/1.03      | k2_relat_1(X0_49) = X1_50 ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_344]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1102,plain,
% 2.03/1.03      ( k2_relat_1(X0_49) = X0_50
% 2.03/1.03      | v3_funct_2(X0_49,X1_50,X0_50) != iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_relat_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3593,plain,
% 2.03/1.03      ( k2_relat_1(sK1) = sK0
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top
% 2.03/1.03      | v1_relat_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1098,c_1102]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_709,plain,
% 2.03/1.03      ( ~ v3_funct_2(sK1,sK0,sK0)
% 2.03/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.03/1.03      | ~ v1_funct_1(sK1)
% 2.03/1.03      | ~ v1_relat_1(sK1)
% 2.03/1.03      | k2_relat_1(sK1) = sK0 ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_607]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3857,plain,
% 2.03/1.03      ( k2_relat_1(sK1) = sK0 ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_3593,c_25,c_23,c_22,c_87,c_709,c_1295]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2,plain,
% 2.03/1.03      ( ~ v1_funct_1(X0)
% 2.03/1.03      | ~ v2_funct_1(X0)
% 2.03/1.03      | ~ v1_relat_1(X0)
% 2.03/1.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.03/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_626,plain,
% 2.03/1.03      ( ~ v1_funct_1(X0_49)
% 2.03/1.03      | ~ v2_funct_1(X0_49)
% 2.03/1.03      | ~ v1_relat_1(X0_49)
% 2.03/1.03      | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1083,plain,
% 2.03/1.03      ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
% 2.03/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v2_funct_1(X0_49) != iProver_top
% 2.03/1.03      | v1_relat_1(X0_49) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1485,plain,
% 2.03/1.03      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 2.03/1.03      | v2_funct_1(sK1) != iProver_top
% 2.03/1.03      | v1_relat_1(sK1) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1101,c_1083]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_666,plain,
% 2.03/1.03      ( ~ v1_funct_1(sK1)
% 2.03/1.03      | ~ v2_funct_1(sK1)
% 2.03/1.03      | ~ v1_relat_1(sK1)
% 2.03/1.03      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_626]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1766,plain,
% 2.03/1.03      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_1485,c_25,c_23,c_22,c_87,c_666,c_680,c_1295]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_3860,plain,
% 2.03/1.03      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_3857,c_1766]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4380,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 2.03/1.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.03/1.03      | v1_funct_1(sK1) != iProver_top ),
% 2.03/1.03      inference(light_normalisation,[status(thm)],[c_4340,c_2424,c_3860]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4031,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 2.03/1.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_4026,c_3148]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4137,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 2.03/1.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.03/1.03      inference(light_normalisation,[status(thm)],[c_4031,c_3860]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4534,plain,
% 2.03/1.03      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_4380,c_2427,c_4137]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_21,negated_conjecture,
% 2.03/1.03      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 2.03/1.03      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 2.03/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_612,negated_conjecture,
% 2.03/1.03      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 2.03/1.03      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1097,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 2.03/1.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_2428,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 2.03/1.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_2424,c_1097]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4537,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 2.03/1.03      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_4534,c_2428]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_8,plain,
% 2.03/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.03/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_621,plain,
% 2.03/1.03      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1088,plain,
% 2.03/1.03      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_6,plain,
% 2.03/1.03      ( r2_relset_1(X0,X1,X2,X2)
% 2.03/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.03/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_623,plain,
% 2.03/1.03      ( r2_relset_1(X0_50,X1_50,X0_49,X0_49)
% 2.03/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.03/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1086,plain,
% 2.03/1.03      ( r2_relset_1(X0_50,X1_50,X0_49,X0_49) = iProver_top
% 2.03/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.03/1.03      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1443,plain,
% 2.03/1.03      ( r2_relset_1(X0_50,X0_50,k6_partfun1(X0_50),k6_partfun1(X0_50)) = iProver_top ),
% 2.03/1.03      inference(superposition,[status(thm)],[c_1088,c_1086]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_1450,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top ),
% 2.03/1.03      inference(instantiation,[status(thm)],[c_1443]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_4540,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.03/1.03      inference(global_propositional_subsumption,
% 2.03/1.03                [status(thm)],
% 2.03/1.03                [c_4537,c_1450]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(c_5965,plain,
% 2.03/1.03      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 2.03/1.03      inference(demodulation,[status(thm)],[c_5962,c_4540]) ).
% 2.03/1.03  
% 2.03/1.03  cnf(contradiction,plain,
% 2.03/1.03      ( $false ),
% 2.03/1.03      inference(minisat,[status(thm)],[c_5965,c_1450]) ).
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/1.03  
% 2.03/1.03  ------                               Statistics
% 2.03/1.03  
% 2.03/1.03  ------ General
% 2.03/1.03  
% 2.03/1.03  abstr_ref_over_cycles:                  0
% 2.03/1.03  abstr_ref_under_cycles:                 0
% 2.03/1.03  gc_basic_clause_elim:                   0
% 2.03/1.03  forced_gc_time:                         0
% 2.03/1.03  parsing_time:                           0.011
% 2.03/1.03  unif_index_cands_time:                  0.
% 2.03/1.03  unif_index_add_time:                    0.
% 2.03/1.03  orderings_time:                         0.
% 2.03/1.03  out_proof_time:                         0.016
% 2.03/1.03  total_time:                             0.248
% 2.03/1.03  num_of_symbols:                         55
% 2.03/1.03  num_of_terms:                           5009
% 2.03/1.03  
% 2.03/1.03  ------ Preprocessing
% 2.03/1.03  
% 2.03/1.03  num_of_splits:                          0
% 2.03/1.03  num_of_split_atoms:                     0
% 2.03/1.03  num_of_reused_defs:                     0
% 2.03/1.03  num_eq_ax_congr_red:                    23
% 2.03/1.03  num_of_sem_filtered_clauses:            1
% 2.03/1.03  num_of_subtypes:                        3
% 2.03/1.03  monotx_restored_types:                  1
% 2.03/1.03  sat_num_of_epr_types:                   0
% 2.03/1.03  sat_num_of_non_cyclic_types:            0
% 2.03/1.03  sat_guarded_non_collapsed_types:        1
% 2.03/1.03  num_pure_diseq_elim:                    0
% 2.03/1.03  simp_replaced_by:                       0
% 2.03/1.03  res_preprocessed:                       126
% 2.03/1.03  prep_upred:                             0
% 2.03/1.03  prep_unflattend:                        6
% 2.03/1.03  smt_new_axioms:                         0
% 2.03/1.03  pred_elim_cands:                        7
% 2.03/1.03  pred_elim:                              2
% 2.03/1.03  pred_elim_cl:                           3
% 2.03/1.03  pred_elim_cycles:                       5
% 2.03/1.03  merged_defs:                            0
% 2.03/1.03  merged_defs_ncl:                        0
% 2.03/1.03  bin_hyper_res:                          0
% 2.03/1.03  prep_cycles:                            4
% 2.03/1.03  pred_elim_time:                         0.005
% 2.03/1.03  splitting_time:                         0.
% 2.03/1.03  sem_filter_time:                        0.
% 2.03/1.03  monotx_time:                            0.001
% 2.03/1.03  subtype_inf_time:                       0.001
% 2.03/1.03  
% 2.03/1.03  ------ Problem properties
% 2.03/1.03  
% 2.03/1.03  clauses:                                22
% 2.03/1.03  conjectures:                            5
% 2.03/1.03  epr:                                    3
% 2.03/1.03  horn:                                   22
% 2.03/1.03  ground:                                 5
% 2.03/1.03  unary:                                  6
% 2.03/1.03  binary:                                 3
% 2.03/1.03  lits:                                   70
% 2.03/1.03  lits_eq:                                8
% 2.03/1.03  fd_pure:                                0
% 2.03/1.03  fd_pseudo:                              0
% 2.03/1.03  fd_cond:                                0
% 2.03/1.03  fd_pseudo_cond:                         2
% 2.03/1.03  ac_symbols:                             0
% 2.03/1.03  
% 2.03/1.03  ------ Propositional Solver
% 2.03/1.03  
% 2.03/1.03  prop_solver_calls:                      30
% 2.03/1.03  prop_fast_solver_calls:                 1105
% 2.03/1.03  smt_solver_calls:                       0
% 2.03/1.03  smt_fast_solver_calls:                  0
% 2.03/1.03  prop_num_of_clauses:                    1660
% 2.03/1.03  prop_preprocess_simplified:             6012
% 2.03/1.03  prop_fo_subsumed:                       60
% 2.03/1.03  prop_solver_time:                       0.
% 2.03/1.03  smt_solver_time:                        0.
% 2.03/1.03  smt_fast_solver_time:                   0.
% 2.03/1.03  prop_fast_solver_time:                  0.
% 2.03/1.03  prop_unsat_core_time:                   0.
% 2.03/1.03  
% 2.03/1.03  ------ QBF
% 2.03/1.03  
% 2.03/1.03  qbf_q_res:                              0
% 2.03/1.03  qbf_num_tautologies:                    0
% 2.03/1.03  qbf_prep_cycles:                        0
% 2.03/1.03  
% 2.03/1.03  ------ BMC1
% 2.03/1.03  
% 2.03/1.03  bmc1_current_bound:                     -1
% 2.03/1.03  bmc1_last_solved_bound:                 -1
% 2.03/1.03  bmc1_unsat_core_size:                   -1
% 2.03/1.03  bmc1_unsat_core_parents_size:           -1
% 2.03/1.03  bmc1_merge_next_fun:                    0
% 2.03/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.03/1.03  
% 2.03/1.03  ------ Instantiation
% 2.03/1.03  
% 2.03/1.03  inst_num_of_clauses:                    593
% 2.03/1.03  inst_num_in_passive:                    182
% 2.03/1.03  inst_num_in_active:                     365
% 2.03/1.03  inst_num_in_unprocessed:                46
% 2.03/1.03  inst_num_of_loops:                      400
% 2.03/1.03  inst_num_of_learning_restarts:          0
% 2.03/1.03  inst_num_moves_active_passive:          30
% 2.03/1.03  inst_lit_activity:                      0
% 2.03/1.03  inst_lit_activity_moves:                0
% 2.03/1.03  inst_num_tautologies:                   0
% 2.03/1.03  inst_num_prop_implied:                  0
% 2.03/1.03  inst_num_existing_simplified:           0
% 2.03/1.03  inst_num_eq_res_simplified:             0
% 2.03/1.03  inst_num_child_elim:                    0
% 2.03/1.03  inst_num_of_dismatching_blockings:      589
% 2.03/1.03  inst_num_of_non_proper_insts:           1115
% 2.03/1.03  inst_num_of_duplicates:                 0
% 2.03/1.03  inst_inst_num_from_inst_to_res:         0
% 2.03/1.03  inst_dismatching_checking_time:         0.
% 2.03/1.03  
% 2.03/1.03  ------ Resolution
% 2.03/1.03  
% 2.03/1.03  res_num_of_clauses:                     0
% 2.03/1.03  res_num_in_passive:                     0
% 2.03/1.03  res_num_in_active:                      0
% 2.03/1.03  res_num_of_loops:                       130
% 2.03/1.03  res_forward_subset_subsumed:            152
% 2.03/1.03  res_backward_subset_subsumed:           4
% 2.03/1.03  res_forward_subsumed:                   0
% 2.03/1.03  res_backward_subsumed:                  0
% 2.03/1.03  res_forward_subsumption_resolution:     1
% 2.03/1.03  res_backward_subsumption_resolution:    0
% 2.03/1.03  res_clause_to_clause_subsumption:       209
% 2.03/1.03  res_orphan_elimination:                 0
% 2.03/1.03  res_tautology_del:                      137
% 2.03/1.03  res_num_eq_res_simplified:              0
% 2.03/1.03  res_num_sel_changes:                    0
% 2.03/1.03  res_moves_from_active_to_pass:          0
% 2.03/1.03  
% 2.03/1.03  ------ Superposition
% 2.03/1.03  
% 2.03/1.03  sup_time_total:                         0.
% 2.03/1.03  sup_time_generating:                    0.
% 2.03/1.03  sup_time_sim_full:                      0.
% 2.03/1.03  sup_time_sim_immed:                     0.
% 2.03/1.03  
% 2.03/1.03  sup_num_of_clauses:                     99
% 2.03/1.03  sup_num_in_active:                      69
% 2.03/1.03  sup_num_in_passive:                     30
% 2.03/1.03  sup_num_of_loops:                       78
% 2.03/1.03  sup_fw_superposition:                   51
% 2.03/1.03  sup_bw_superposition:                   33
% 2.03/1.03  sup_immediate_simplified:               10
% 2.03/1.03  sup_given_eliminated:                   0
% 2.03/1.03  comparisons_done:                       0
% 2.03/1.03  comparisons_avoided:                    0
% 2.03/1.03  
% 2.03/1.03  ------ Simplifications
% 2.03/1.03  
% 2.03/1.03  
% 2.03/1.03  sim_fw_subset_subsumed:                 0
% 2.03/1.03  sim_bw_subset_subsumed:                 3
% 2.03/1.03  sim_fw_subsumed:                        1
% 2.03/1.03  sim_bw_subsumed:                        0
% 2.03/1.03  sim_fw_subsumption_res:                 2
% 2.03/1.03  sim_bw_subsumption_res:                 0
% 2.03/1.03  sim_tautology_del:                      0
% 2.03/1.03  sim_eq_tautology_del:                   3
% 2.03/1.03  sim_eq_res_simp:                        0
% 2.03/1.03  sim_fw_demodulated:                     4
% 2.03/1.03  sim_bw_demodulated:                     10
% 2.03/1.03  sim_light_normalised:                   9
% 2.03/1.03  sim_joinable_taut:                      0
% 2.03/1.03  sim_joinable_simp:                      0
% 2.03/1.03  sim_ac_normalised:                      0
% 2.03/1.03  sim_smt_subsumption:                    0
% 2.03/1.03  
%------------------------------------------------------------------------------
