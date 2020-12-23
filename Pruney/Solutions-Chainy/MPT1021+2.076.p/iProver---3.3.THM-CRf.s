%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:34 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  192 (1028 expanded)
%              Number of clauses        :  126 ( 348 expanded)
%              Number of leaves         :   21 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          :  651 (4822 expanded)
%              Number of equality atoms :  252 ( 556 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f43])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f65])).

cnf(c_631,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1399,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_3065,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_4756,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_4760,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4756])).

cnf(c_640,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2203,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_3187,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_4578,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3187])).

cnf(c_4581,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_4578])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_609,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1096,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_617,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1088,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1092,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2947,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1092])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3083,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_26])).

cnf(c_3084,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3083])).

cnf(c_3091,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_3084])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_614,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_691,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_4249,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3091,c_691])).

cnf(c_4250,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4249])).

cnf(c_4260,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_4250])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1093,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2129,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1093])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_698,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_2356,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_25,c_24,c_23,c_22,c_698])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_611,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1094,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1937,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1094])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1084,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1433,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1096,c_1084])).

cnf(c_1956,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1937,c_1433])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2545,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_26,c_27])).

cnf(c_606,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1099,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_622,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1083,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1482,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1083])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_84,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_670,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_618,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_680,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1287,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1289,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_1711,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1482,c_25,c_23,c_22,c_84,c_670,c_680,c_1289])).

cnf(c_2548,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2545,c_1711])).

cnf(c_4309,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4260,c_2356,c_2548])).

cnf(c_1091,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1973,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1091])).

cnf(c_28,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_693,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_2285,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1973,c_26,c_27,c_28,c_29,c_693])).

cnf(c_2359,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2356,c_2285])).

cnf(c_2661,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_1088])).

cnf(c_4015,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_26,c_27,c_28,c_29])).

cnf(c_4020,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4015,c_3084])).

cnf(c_4111,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4020,c_2548])).

cnf(c_4326,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4309,c_2359,c_4111])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_610,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1095,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2360,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2356,c_1095])).

cnf(c_4329,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4326,c_2360])).

cnf(c_4330,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4329])).

cnf(c_3368,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_3371,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3368])).

cnf(c_2790,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2661])).

cnf(c_2367,plain,
    ( v1_funct_1(k2_funct_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2359])).

cnf(c_632,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2066,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2067,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_638,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1373,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1899,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_1900,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_1371,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1501,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1588,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_1589,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_8,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_619,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1086,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_620,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1085,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_1557,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1085])).

cnf(c_1572,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1557])).

cnf(c_1574,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_326,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_327,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_343,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_327,c_5])).

cnf(c_605,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_709,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_623,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_667,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_629,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_659,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_650,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4760,c_4581,c_4330,c_3371,c_2790,c_2367,c_2067,c_1900,c_1589,c_1574,c_1289,c_709,c_680,c_667,c_659,c_650,c_84,c_22,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.00  
% 2.73/1.00  ------  iProver source info
% 2.73/1.00  
% 2.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.00  git: non_committed_changes: false
% 2.73/1.00  git: last_make_outside_of_git: false
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     num_symb
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       true
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  ------ Parsing...
% 2.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.00  ------ Proving...
% 2.73/1.00  ------ Problem Properties 
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  clauses                                 22
% 2.73/1.00  conjectures                             5
% 2.73/1.00  EPR                                     3
% 2.73/1.00  Horn                                    22
% 2.73/1.00  unary                                   7
% 2.73/1.00  binary                                  2
% 2.73/1.00  lits                                    68
% 2.73/1.00  lits eq                                 7
% 2.73/1.00  fd_pure                                 0
% 2.73/1.00  fd_pseudo                               0
% 2.73/1.00  fd_cond                                 0
% 2.73/1.00  fd_pseudo_cond                          1
% 2.73/1.00  AC symbols                              0
% 2.73/1.00  
% 2.73/1.00  ------ Schedule dynamic 5 is on 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  Current options:
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     none
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       false
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ Proving...
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS status Theorem for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  fof(f16,conjecture,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f17,negated_conjecture,(
% 2.73/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.73/1.00    inference(negated_conjecture,[],[f16])).
% 2.73/1.00  
% 2.73/1.00  fof(f38,plain,(
% 2.73/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f17])).
% 2.73/1.00  
% 2.73/1.00  fof(f39,plain,(
% 2.73/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.73/1.00    inference(flattening,[],[f38])).
% 2.73/1.00  
% 2.73/1.00  fof(f43,plain,(
% 2.73/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f44,plain,(
% 2.73/1.00    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f43])).
% 2.73/1.00  
% 2.73/1.00  fof(f70,plain,(
% 2.73/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.73/1.00    inference(cnf_transformation,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f11,axiom,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f30,plain,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f11])).
% 2.73/1.00  
% 2.73/1.00  fof(f31,plain,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.73/1.00    inference(flattening,[],[f30])).
% 2.73/1.00  
% 2.73/1.00  fof(f62,plain,(
% 2.73/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f12,axiom,(
% 2.73/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f32,plain,(
% 2.73/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.73/1.00    inference(ennf_transformation,[],[f12])).
% 2.73/1.00  
% 2.73/1.00  fof(f33,plain,(
% 2.73/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.73/1.00    inference(flattening,[],[f32])).
% 2.73/1.00  
% 2.73/1.00  fof(f63,plain,(
% 2.73/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f33])).
% 2.73/1.00  
% 2.73/1.00  fof(f67,plain,(
% 2.73/1.00    v1_funct_1(sK2)),
% 2.73/1.00    inference(cnf_transformation,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f59,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f13,axiom,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f34,plain,(
% 2.73/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f13])).
% 2.73/1.00  
% 2.73/1.00  fof(f35,plain,(
% 2.73/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.73/1.00    inference(flattening,[],[f34])).
% 2.73/1.00  
% 2.73/1.00  fof(f64,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f35])).
% 2.73/1.00  
% 2.73/1.00  fof(f68,plain,(
% 2.73/1.00    v1_funct_2(sK2,sK1,sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f69,plain,(
% 2.73/1.00    v3_funct_2(sK2,sK1,sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f15,axiom,(
% 2.73/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f36,plain,(
% 2.73/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f15])).
% 2.73/1.00  
% 2.73/1.00  fof(f37,plain,(
% 2.73/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.73/1.00    inference(flattening,[],[f36])).
% 2.73/1.00  
% 2.73/1.00  fof(f66,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f37])).
% 2.73/1.00  
% 2.73/1.00  fof(f6,axiom,(
% 2.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f23,plain,(
% 2.73/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.00    inference(ennf_transformation,[],[f6])).
% 2.73/1.00  
% 2.73/1.00  fof(f51,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f23])).
% 2.73/1.00  
% 2.73/1.00  fof(f4,axiom,(
% 2.73/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f20,plain,(
% 2.73/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f4])).
% 2.73/1.00  
% 2.73/1.00  fof(f21,plain,(
% 2.73/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/1.00    inference(flattening,[],[f20])).
% 2.73/1.00  
% 2.73/1.00  fof(f48,plain,(
% 2.73/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f21])).
% 2.73/1.00  
% 2.73/1.00  fof(f14,axiom,(
% 2.73/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f65,plain,(
% 2.73/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f14])).
% 2.73/1.00  
% 2.73/1.00  fof(f73,plain,(
% 2.73/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(definition_unfolding,[],[f48,f65])).
% 2.73/1.00  
% 2.73/1.00  fof(f3,axiom,(
% 2.73/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f47,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f3])).
% 2.73/1.00  
% 2.73/1.00  fof(f9,axiom,(
% 2.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f26,plain,(
% 2.73/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.00    inference(ennf_transformation,[],[f9])).
% 2.73/1.00  
% 2.73/1.00  fof(f27,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.00    inference(flattening,[],[f26])).
% 2.73/1.00  
% 2.73/1.00  fof(f55,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f27])).
% 2.73/1.00  
% 2.73/1.00  fof(f2,axiom,(
% 2.73/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f19,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.73/1.00    inference(ennf_transformation,[],[f2])).
% 2.73/1.00  
% 2.73/1.00  fof(f46,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f19])).
% 2.73/1.00  
% 2.73/1.00  fof(f71,plain,(
% 2.73/1.00    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.73/1.00    inference(cnf_transformation,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f8,axiom,(
% 2.73/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f53,plain,(
% 2.73/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f8])).
% 2.73/1.00  
% 2.73/1.00  fof(f74,plain,(
% 2.73/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.73/1.00    inference(definition_unfolding,[],[f53,f65])).
% 2.73/1.00  
% 2.73/1.00  fof(f7,axiom,(
% 2.73/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f24,plain,(
% 2.73/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.73/1.00    inference(ennf_transformation,[],[f7])).
% 2.73/1.00  
% 2.73/1.00  fof(f25,plain,(
% 2.73/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.00    inference(flattening,[],[f24])).
% 2.73/1.00  
% 2.73/1.00  fof(f52,plain,(
% 2.73/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f56,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f27])).
% 2.73/1.00  
% 2.73/1.00  fof(f10,axiom,(
% 2.73/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f28,plain,(
% 2.73/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.73/1.00    inference(ennf_transformation,[],[f10])).
% 2.73/1.00  
% 2.73/1.00  fof(f29,plain,(
% 2.73/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/1.00    inference(flattening,[],[f28])).
% 2.73/1.00  
% 2.73/1.00  fof(f42,plain,(
% 2.73/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/1.00    inference(nnf_transformation,[],[f29])).
% 2.73/1.00  
% 2.73/1.00  fof(f57,plain,(
% 2.73/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f42])).
% 2.73/1.00  
% 2.73/1.00  fof(f5,axiom,(
% 2.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f18,plain,(
% 2.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.73/1.00    inference(pure_predicate_removal,[],[f5])).
% 2.73/1.00  
% 2.73/1.00  fof(f22,plain,(
% 2.73/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.00    inference(ennf_transformation,[],[f18])).
% 2.73/1.00  
% 2.73/1.00  fof(f50,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f22])).
% 2.73/1.00  
% 2.73/1.00  fof(f49,plain,(
% 2.73/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f21])).
% 2.73/1.00  
% 2.73/1.00  fof(f72,plain,(
% 2.73/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.00    inference(definition_unfolding,[],[f49,f65])).
% 2.73/1.00  
% 2.73/1.00  cnf(c_631,plain,
% 2.73/1.00      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.73/1.00      theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1399,plain,
% 2.73/1.00      ( X0_50 != X1_50
% 2.73/1.00      | X0_50 = k6_partfun1(X0_51)
% 2.73/1.00      | k6_partfun1(X0_51) != X1_50 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_631]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3065,plain,
% 2.73/1.00      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 2.73/1.00      | X0_50 = k6_partfun1(sK1)
% 2.73/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1399]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4756,plain,
% 2.73/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.73/1.00      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.73/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_3065]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4760,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.73/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.73/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_4756]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_640,plain,
% 2.73/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.73/1.00      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 2.73/1.00      | X2_51 != X0_51
% 2.73/1.00      | X3_51 != X1_51
% 2.73/1.00      | X2_50 != X0_50
% 2.73/1.00      | X3_50 != X1_50 ),
% 2.73/1.00      theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2203,plain,
% 2.73/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.73/1.00      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 2.73/1.00      | X2_51 != X0_51
% 2.73/1.00      | X3_51 != X1_51
% 2.73/1.00      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 2.73/1.00      | k6_partfun1(X8_51) != X1_50 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_640]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3187,plain,
% 2.73/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 2.73/1.00      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 2.73/1.00      | X3_51 != X0_51
% 2.73/1.00      | X4_51 != X1_51
% 2.73/1.00      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 2.73/1.00      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_2203]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4578,plain,
% 2.73/1.00      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 2.73/1.00      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 2.73/1.00      | X0_51 != X7_51
% 2.73/1.00      | X1_51 != X8_51
% 2.73/1.00      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 2.73/1.00      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_3187]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4581,plain,
% 2.73/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 2.73/1.00      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 2.73/1.00      | sK1 != sK1
% 2.73/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 2.73/1.00      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_4578]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,negated_conjecture,
% 2.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.73/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_609,negated_conjecture,
% 2.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1096,plain,
% 2.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_14,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_617,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.73/1.00      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1088,plain,
% 2.73/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_18,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X3)
% 2.73/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_613,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | ~ v1_funct_1(X1_50)
% 2.73/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1092,plain,
% 2.73/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 2.73/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_funct_1(X1_50) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2947,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_1092]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_25,negated_conjecture,
% 2.73/1.00      ( v1_funct_1(sK2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_26,plain,
% 2.73/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3083,plain,
% 2.73/1.00      ( v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.73/1.00      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2947,c_26]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3084,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_3083]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3091,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
% 2.73/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1088,c_3084]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_17,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_614,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_691,plain,
% 2.73/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4249,plain,
% 2.73/1.00      ( v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3091,c_691]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4250,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
% 2.73/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_4249]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4260,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 2.73/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_4250]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_19,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_612,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1093,plain,
% 2.73/1.00      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 2.73/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2129,plain,
% 2.73/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.73/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_1093]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_24,negated_conjecture,
% 2.73/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_23,negated_conjecture,
% 2.73/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_698,plain,
% 2.73/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_612]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2356,plain,
% 2.73/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2129,c_25,c_24,c_23,c_22,c_698]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.73/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_611,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1094,plain,
% 2.73/1.00      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 2.73/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1937,plain,
% 2.73/1.00      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.73/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_1094]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_621,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1084,plain,
% 2.73/1.00      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1433,plain,
% 2.73/1.00      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_1084]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1956,plain,
% 2.73/1.00      ( k1_relat_1(sK2) = sK1
% 2.73/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_1937,c_1433]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_27,plain,
% 2.73/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2545,plain,
% 2.73/1.00      ( k1_relat_1(sK2) = sK1 ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1956,c_26,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_606,negated_conjecture,
% 2.73/1.00      ( v1_funct_1(sK2) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1099,plain,
% 2.73/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4,plain,
% 2.73/1.00      ( ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v2_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_622,plain,
% 2.73/1.00      ( ~ v1_funct_1(X0_50)
% 2.73/1.00      | ~ v2_funct_1(X0_50)
% 2.73/1.00      | ~ v1_relat_1(X0_50)
% 2.73/1.00      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1083,plain,
% 2.73/1.00      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v2_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1482,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.73/1.00      | v2_funct_1(sK2) != iProver_top
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1099,c_1083]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2,plain,
% 2.73/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_84,plain,
% 2.73/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_670,plain,
% 2.73/1.00      ( ~ v1_funct_1(sK2)
% 2.73/1.00      | ~ v2_funct_1(sK2)
% 2.73/1.00      | ~ v1_relat_1(sK2)
% 2.73/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_622]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_10,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | v2_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_618,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | v2_funct_1(X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_680,plain,
% 2.73/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | v2_funct_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_618]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.73/1.00      | ~ v1_relat_1(X1)
% 2.73/1.00      | v1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_625,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.73/1.00      | ~ v1_relat_1(X1_50)
% 2.73/1.00      | v1_relat_1(X0_50) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1287,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | v1_relat_1(X0_50)
% 2.73/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1289,plain,
% 2.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 2.73/1.00      | v1_relat_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1711,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1482,c_25,c_23,c_22,c_84,c_670,c_680,c_1289]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2548,plain,
% 2.73/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_2545,c_1711]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4309,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.73/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4260,c_2356,c_2548]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1091,plain,
% 2.73/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.73/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1973,plain,
% 2.73/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1096,c_1091]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_28,plain,
% 2.73/1.00      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_29,plain,
% 2.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_693,plain,
% 2.73/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_691]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2285,plain,
% 2.73/1.00      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1973,c_26,c_27,c_28,c_29,c_693]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2359,plain,
% 2.73/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_2356,c_2285]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2661,plain,
% 2.73/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.73/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_2356,c_1088]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4015,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2661,c_26,c_27,c_28,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4020,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4015,c_3084]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4111,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4020,c_2548]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4326,plain,
% 2.73/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4309,c_2359,c_4111]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_21,negated_conjecture,
% 2.73/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.73/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_610,negated_conjecture,
% 2.73/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.73/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1095,plain,
% 2.73/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.73/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2360,plain,
% 2.73/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.73/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_2356,c_1095]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4329,plain,
% 2.73/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.73/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4326,c_2360]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4330,plain,
% 2.73/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 2.73/1.00      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
% 2.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4329]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3368,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_613]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3371,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_3368]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2790,plain,
% 2.73/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_funct_1(sK2) ),
% 2.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2661]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2367,plain,
% 2.73/1.00      ( v1_funct_1(k2_funct_1(sK2)) ),
% 2.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2359]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_632,plain,
% 2.73/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.73/1.00      theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2066,plain,
% 2.73/1.00      ( k2_relat_1(X0_50) != X0_51
% 2.73/1.00      | sK1 != X0_51
% 2.73/1.00      | sK1 = k2_relat_1(X0_50) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2067,plain,
% 2.73/1.00      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_2066]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_638,plain,
% 2.73/1.00      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 2.73/1.00      theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1373,plain,
% 2.73/1.00      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1899,plain,
% 2.73/1.00      ( sK1 != k2_relat_1(X0_50)
% 2.73/1.00      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1373]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1900,plain,
% 2.73/1.00      ( sK1 != k2_relat_1(sK2)
% 2.73/1.00      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1899]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1371,plain,
% 2.73/1.00      ( X0_50 != X1_50
% 2.73/1.00      | k6_partfun1(sK1) != X1_50
% 2.73/1.00      | k6_partfun1(sK1) = X0_50 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_631]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1501,plain,
% 2.73/1.00      ( X0_50 != k6_partfun1(X0_51)
% 2.73/1.00      | k6_partfun1(sK1) = X0_50
% 2.73/1.00      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1371]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1588,plain,
% 2.73/1.00      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 2.73/1.00      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 2.73/1.00      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1501]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1589,plain,
% 2.73/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 2.73/1.00      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.73/1.00      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1588]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_8,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.73/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_619,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1086,plain,
% 2.73/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_7,plain,
% 2.73/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.73/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_620,plain,
% 2.73/1.00      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1085,plain,
% 2.73/1.00      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.73/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1557,plain,
% 2.73/1.00      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 2.73/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1086,c_1085]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1572,plain,
% 2.73/1.00      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51))
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.73/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1557]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1574,plain,
% 2.73/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1572]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.73/1.00      | v2_funct_2(X0,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_13,plain,
% 2.73/1.00      ( ~ v2_funct_2(X0,X1)
% 2.73/1.00      | ~ v5_relat_1(X0,X1)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k2_relat_1(X0) = X1 ),
% 2.73/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_326,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ v5_relat_1(X3,X4)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X3)
% 2.73/1.00      | X3 != X0
% 2.73/1.00      | X4 != X2
% 2.73/1.00      | k2_relat_1(X3) = X4 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_327,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ v5_relat_1(X0,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k2_relat_1(X0) = X2 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_326]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5,plain,
% 2.73/1.00      ( v5_relat_1(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_343,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k2_relat_1(X0) = X2 ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_327,c_5]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_605,plain,
% 2.73/1.00      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.73/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.73/1.00      | ~ v1_funct_1(X0_50)
% 2.73/1.00      | ~ v1_relat_1(X0_50)
% 2.73/1.00      | k2_relat_1(X0_50) = X1_51 ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_343]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_709,plain,
% 2.73/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | ~ v1_relat_1(sK2)
% 2.73/1.00      | k2_relat_1(sK2) = sK1 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_605]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3,plain,
% 2.73/1.00      ( ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v2_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_623,plain,
% 2.73/1.00      ( ~ v1_funct_1(X0_50)
% 2.73/1.00      | ~ v2_funct_1(X0_50)
% 2.73/1.00      | ~ v1_relat_1(X0_50)
% 2.73/1.00      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.73/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_667,plain,
% 2.73/1.00      ( ~ v1_funct_1(sK2)
% 2.73/1.00      | ~ v2_funct_1(sK2)
% 2.73/1.00      | ~ v1_relat_1(sK2)
% 2.73/1.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_623]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_629,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_659,plain,
% 2.73/1.00      ( sK1 = sK1 ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_629]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_650,plain,
% 2.73/1.00      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(contradiction,plain,
% 2.73/1.00      ( $false ),
% 2.73/1.00      inference(minisat,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4760,c_4581,c_4330,c_3371,c_2790,c_2367,c_2067,c_1900,
% 2.73/1.00                 c_1589,c_1574,c_1289,c_709,c_680,c_667,c_659,c_650,c_84,
% 2.73/1.00                 c_22,c_23,c_24,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.016
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.01
% 2.73/1.00  total_time:                             0.248
% 2.73/1.00  num_of_symbols:                         56
% 2.73/1.00  num_of_terms:                           4225
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    26
% 2.73/1.00  num_of_sem_filtered_clauses:            1
% 2.73/1.00  num_of_subtypes:                        3
% 2.73/1.00  monotx_restored_types:                  1
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       126
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        6
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        7
% 2.73/1.00  pred_elim:                              2
% 2.73/1.00  pred_elim_cl:                           3
% 2.73/1.00  pred_elim_cycles:                       5
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            4
% 2.73/1.00  pred_elim_time:                         0.006
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.001
% 2.73/1.00  subtype_inf_time:                       0.002
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                22
% 2.73/1.00  conjectures:                            5
% 2.73/1.00  epr:                                    3
% 2.73/1.00  horn:                                   22
% 2.73/1.00  ground:                                 5
% 2.73/1.00  unary:                                  7
% 2.73/1.00  binary:                                 2
% 2.73/1.00  lits:                                   68
% 2.73/1.00  lits_eq:                                7
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                0
% 2.73/1.00  fd_pseudo_cond:                         1
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      29
% 2.73/1.00  prop_fast_solver_calls:                 1022
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    1358
% 2.73/1.00  prop_preprocess_simplified:             5311
% 2.73/1.00  prop_fo_subsumed:                       47
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    471
% 2.73/1.00  inst_num_in_passive:                    47
% 2.73/1.00  inst_num_in_active:                     301
% 2.73/1.00  inst_num_in_unprocessed:                122
% 2.73/1.00  inst_num_of_loops:                      324
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          18
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                0
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      419
% 2.73/1.00  inst_num_of_non_proper_insts:           691
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       130
% 2.73/1.00  res_forward_subset_subsumed:            120
% 2.73/1.00  res_backward_subset_subsumed:           4
% 2.73/1.00  res_forward_subsumed:                   0
% 2.73/1.00  res_backward_subsumed:                  0
% 2.73/1.00  res_forward_subsumption_resolution:     1
% 2.73/1.00  res_backward_subsumption_resolution:    0
% 2.73/1.00  res_clause_to_clause_subsumption:       171
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      97
% 2.73/1.00  res_num_eq_res_simplified:              0
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     91
% 2.73/1.00  sup_num_in_active:                      55
% 2.73/1.00  sup_num_in_passive:                     36
% 2.73/1.00  sup_num_of_loops:                       64
% 2.73/1.00  sup_fw_superposition:                   56
% 2.73/1.00  sup_bw_superposition:                   24
% 2.73/1.00  sup_immediate_simplified:               14
% 2.73/1.00  sup_given_eliminated:                   0
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    0
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 1
% 2.73/1.00  sim_bw_subset_subsumed:                 7
% 2.73/1.00  sim_fw_subsumed:                        4
% 2.73/1.00  sim_bw_subsumed:                        0
% 2.73/1.00  sim_fw_subsumption_res:                 2
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      0
% 2.73/1.00  sim_eq_tautology_del:                   0
% 2.73/1.00  sim_eq_res_simp:                        0
% 2.73/1.00  sim_fw_demodulated:                     2
% 2.73/1.00  sim_bw_demodulated:                     8
% 2.73/1.00  sim_light_normalised:                   6
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------
