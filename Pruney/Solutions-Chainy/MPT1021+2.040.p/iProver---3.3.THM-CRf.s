%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:26 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 888 expanded)
%              Number of clauses        :  139 ( 324 expanded)
%              Number of leaves         :   23 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          :  689 (4142 expanded)
%              Number of equality atoms :  289 ( 527 expanded)
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

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f71,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

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
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f60,plain,(
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

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f67])).

cnf(c_784,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1538,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_3158,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_4691,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3158])).

cnf(c_4695,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4691])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_760,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1267,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_762,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1265,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2221,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1265])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1252,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1646,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1267,c_1252])).

cnf(c_2241,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2221,c_1646])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2806,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2241,c_28,c_29])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1251,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_1632,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1251])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_777,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1250,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_1737,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1250])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_819,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_822,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_772,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_832,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1822,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_27,c_25,c_24,c_819,c_822,c_832])).

cnf(c_2809,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2806,c_1822])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_763,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1264,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_2365,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1264])).

cnf(c_853,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2555,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2365,c_27,c_26,c_25,c_24,c_853])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_771,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1256,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_2886,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_1256])).

cnf(c_30,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_834,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_836,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_782,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1501,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1559,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_2(X0_51,X2_50)
    | k2_funct_2(X0_51,X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1663,plain,
    ( X0_50 = k2_funct_2(X0_51,X1_50)
    | X0_50 != k2_funct_1(X1_50)
    | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_1798,plain,
    ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
    | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
    | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1800,plain,
    ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_780,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1799,plain,
    ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1801,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1486,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | X0_50 != k2_funct_2(X0_51,X1_50) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_1(X0_50),X0_52)
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2787,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2788,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50)
    | m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_2790,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(sK2) != k2_funct_2(sK1,sK2)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_3813,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_836,c_853,c_1501,c_1800,c_1801,c_2790])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1263,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_3230,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1263])).

cnf(c_3361,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3230,c_28])).

cnf(c_3362,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3361])).

cnf(c_3818,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_3362])).

cnf(c_835,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_768,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1259,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_2325,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1259])).

cnf(c_843,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_845,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_2549,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_28,c_29,c_30,c_31,c_845])).

cnf(c_2558,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_2549])).

cnf(c_2566,plain,
    ( v1_funct_1(k2_funct_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2558])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_3792,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(X0_50))
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_3795,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3792])).

cnf(c_4020,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_27,c_26,c_25,c_24,c_835,c_853,c_1501,c_1800,c_1801,c_2566,c_2789,c_3795])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_761,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1266,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_2559,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_1266])).

cnf(c_4023,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4020,c_2559])).

cnf(c_4523,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2809,c_4023])).

cnf(c_793,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2295,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_3437,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_4325,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(c_4327,plain,
    ( X0_51 != X1_51
    | X2_51 != X3_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
    | k6_partfun1(X9_51) != k6_partfun1(X8_51)
    | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
    | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4325])).

cnf(c_4329,plain,
    ( sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_3591,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_3594,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3591])).

cnf(c_785,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2165,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2166,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_6,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_773,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1254,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_774,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1253,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_2074,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1253])).

cnf(c_2092,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_787,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1519,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1987,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1988,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_1517,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1599,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_1692,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_1693,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_312,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_313,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_2])).

cnf(c_318,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_333,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_318,c_3])).

cnf(c_756,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_864,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_778,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_816,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_781,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_812,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_799,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4695,c_4523,c_4329,c_3594,c_2789,c_2566,c_2166,c_2092,c_1988,c_1801,c_1800,c_1693,c_1501,c_864,c_853,c_835,c_832,c_822,c_816,c_812,c_799,c_31,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:31 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 2.89/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.98  
% 2.89/0.98  ------  iProver source info
% 2.89/0.98  
% 2.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.98  git: non_committed_changes: false
% 2.89/0.98  git: last_make_outside_of_git: false
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     num_symb
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       true
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  ------ Parsing...
% 2.89/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.98  ------ Proving...
% 2.89/0.98  ------ Problem Properties 
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  clauses                                 23
% 2.89/0.98  conjectures                             5
% 2.89/0.98  EPR                                     3
% 2.89/0.98  Horn                                    23
% 2.89/0.98  unary                                   8
% 2.89/0.98  binary                                  3
% 2.89/0.98  lits                                    67
% 2.89/0.98  lits eq                                 7
% 2.89/0.98  fd_pure                                 0
% 2.89/0.98  fd_pseudo                               0
% 2.89/0.98  fd_cond                                 0
% 2.89/0.98  fd_pseudo_cond                          1
% 2.89/0.98  AC symbols                              0
% 2.89/0.98  
% 2.89/0.98  ------ Schedule dynamic 5 is on 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  Current options:
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     none
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       false
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ Proving...
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  % SZS status Theorem for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  fof(f15,conjecture,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f16,negated_conjecture,(
% 2.89/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.89/0.98    inference(negated_conjecture,[],[f15])).
% 2.89/0.98  
% 2.89/0.98  fof(f38,plain,(
% 2.89/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.89/0.98    inference(ennf_transformation,[],[f16])).
% 2.89/0.98  
% 2.89/0.98  fof(f39,plain,(
% 2.89/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.89/0.98    inference(flattening,[],[f38])).
% 2.89/0.98  
% 2.89/0.98  fof(f43,plain,(
% 2.89/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f44,plain,(
% 2.89/0.98    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f43])).
% 2.89/0.98  
% 2.89/0.98  fof(f72,plain,(
% 2.89/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.89/0.98    inference(cnf_transformation,[],[f44])).
% 2.89/0.98  
% 2.89/0.98  fof(f14,axiom,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f36,plain,(
% 2.89/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.89/0.98    inference(ennf_transformation,[],[f14])).
% 2.89/0.98  
% 2.89/0.98  fof(f37,plain,(
% 2.89/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.89/0.98    inference(flattening,[],[f36])).
% 2.89/0.98  
% 2.89/0.98  fof(f68,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f37])).
% 2.89/0.98  
% 2.89/0.98  fof(f4,axiom,(
% 2.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f23,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(ennf_transformation,[],[f4])).
% 2.89/0.98  
% 2.89/0.98  fof(f49,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f23])).
% 2.89/0.98  
% 2.89/0.98  fof(f69,plain,(
% 2.89/0.98    v1_funct_1(sK2)),
% 2.89/0.98    inference(cnf_transformation,[],[f44])).
% 2.89/0.98  
% 2.89/0.98  fof(f70,plain,(
% 2.89/0.98    v1_funct_2(sK2,sK1,sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f44])).
% 2.89/0.98  
% 2.89/0.98  fof(f2,axiom,(
% 2.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f21,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(ennf_transformation,[],[f2])).
% 2.89/0.98  
% 2.89/0.98  fof(f47,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f21])).
% 2.89/0.98  
% 2.89/0.98  fof(f1,axiom,(
% 2.89/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f19,plain,(
% 2.89/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.89/0.98    inference(ennf_transformation,[],[f1])).
% 2.89/0.98  
% 2.89/0.98  fof(f20,plain,(
% 2.89/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/0.98    inference(flattening,[],[f19])).
% 2.89/0.98  
% 2.89/0.98  fof(f45,plain,(
% 2.89/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f20])).
% 2.89/0.98  
% 2.89/0.98  fof(f13,axiom,(
% 2.89/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f67,plain,(
% 2.89/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f13])).
% 2.89/0.98  
% 2.89/0.98  fof(f75,plain,(
% 2.89/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.98    inference(definition_unfolding,[],[f45,f67])).
% 2.89/0.98  
% 2.89/0.98  fof(f71,plain,(
% 2.89/0.98    v3_funct_2(sK2,sK1,sK1)),
% 2.89/0.98    inference(cnf_transformation,[],[f44])).
% 2.89/0.98  
% 2.89/0.98  fof(f7,axiom,(
% 2.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f26,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(ennf_transformation,[],[f7])).
% 2.89/0.98  
% 2.89/0.98  fof(f27,plain,(
% 2.89/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(flattening,[],[f26])).
% 2.89/0.98  
% 2.89/0.98  fof(f53,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f27])).
% 2.89/0.98  
% 2.89/0.98  fof(f12,axiom,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f34,plain,(
% 2.89/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.89/0.98    inference(ennf_transformation,[],[f12])).
% 2.89/0.98  
% 2.89/0.98  fof(f35,plain,(
% 2.89/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.89/0.98    inference(flattening,[],[f34])).
% 2.89/0.98  
% 2.89/0.98  fof(f66,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f35])).
% 2.89/0.98  
% 2.89/0.98  fof(f9,axiom,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f30,plain,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.89/0.98    inference(ennf_transformation,[],[f9])).
% 2.89/0.98  
% 2.89/0.98  fof(f31,plain,(
% 2.89/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.89/0.98    inference(flattening,[],[f30])).
% 2.89/0.98  
% 2.89/0.98  fof(f60,plain,(
% 2.89/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f31])).
% 2.89/0.98  
% 2.89/0.98  fof(f11,axiom,(
% 2.89/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f32,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.89/0.98    inference(ennf_transformation,[],[f11])).
% 2.89/0.98  
% 2.89/0.98  fof(f33,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.89/0.98    inference(flattening,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f65,plain,(
% 2.89/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f33])).
% 2.89/0.98  
% 2.89/0.98  fof(f57,plain,(
% 2.89/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f31])).
% 2.89/0.98  
% 2.89/0.98  fof(f73,plain,(
% 2.89/0.98    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.89/0.98    inference(cnf_transformation,[],[f44])).
% 2.89/0.98  
% 2.89/0.98  fof(f6,axiom,(
% 2.89/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f51,plain,(
% 2.89/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f6])).
% 2.89/0.98  
% 2.89/0.98  fof(f76,plain,(
% 2.89/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.89/0.98    inference(definition_unfolding,[],[f51,f67])).
% 2.89/0.98  
% 2.89/0.98  fof(f5,axiom,(
% 2.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f24,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.89/0.98    inference(ennf_transformation,[],[f5])).
% 2.89/0.98  
% 2.89/0.98  fof(f25,plain,(
% 2.89/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(flattening,[],[f24])).
% 2.89/0.98  
% 2.89/0.98  fof(f50,plain,(
% 2.89/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f25])).
% 2.89/0.98  
% 2.89/0.98  fof(f54,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f27])).
% 2.89/0.98  
% 2.89/0.98  fof(f8,axiom,(
% 2.89/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f28,plain,(
% 2.89/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.89/0.98    inference(ennf_transformation,[],[f8])).
% 2.89/0.98  
% 2.89/0.98  fof(f29,plain,(
% 2.89/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.89/0.98    inference(flattening,[],[f28])).
% 2.89/0.98  
% 2.89/0.98  fof(f40,plain,(
% 2.89/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.89/0.98    inference(nnf_transformation,[],[f29])).
% 2.89/0.98  
% 2.89/0.98  fof(f55,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f40])).
% 2.89/0.98  
% 2.89/0.98  fof(f3,axiom,(
% 2.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f18,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.89/0.98    inference(pure_predicate_removal,[],[f3])).
% 2.89/0.98  
% 2.89/0.98  fof(f22,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.98    inference(ennf_transformation,[],[f18])).
% 2.89/0.98  
% 2.89/0.98  fof(f48,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f22])).
% 2.89/0.98  
% 2.89/0.98  fof(f46,plain,(
% 2.89/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f20])).
% 2.89/0.98  
% 2.89/0.98  fof(f74,plain,(
% 2.89/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.98    inference(definition_unfolding,[],[f46,f67])).
% 2.89/0.98  
% 2.89/0.98  cnf(c_784,plain,
% 2.89/0.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.89/0.98      theory(equality) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1538,plain,
% 2.89/0.98      ( X0_50 != X1_50
% 2.89/0.98      | X0_50 = k6_partfun1(X0_51)
% 2.89/0.98      | k6_partfun1(X0_51) != X1_50 ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_784]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3158,plain,
% 2.89/0.98      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 2.89/0.98      | X0_50 = k6_partfun1(sK1)
% 2.89/0.98      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_1538]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4691,plain,
% 2.89/0.98      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.89/0.98      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.89/0.98      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.89/0.98      inference(instantiation,[status(thm)],[c_3158]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4695,plain,
% 2.89/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.89/0.98      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.89/0.99      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_4691]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_24,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_760,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1267,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_22,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.89/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_762,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1265,plain,
% 2.89/0.99      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 2.89/0.99      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2221,plain,
% 2.89/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.89/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1265]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_775,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1252,plain,
% 2.89/0.99      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1646,plain,
% 2.89/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1252]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2241,plain,
% 2.89/0.99      ( k1_relat_1(sK2) = sK1
% 2.89/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_2221,c_1646]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_27,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_28,plain,
% 2.89/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_26,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_29,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2806,plain,
% 2.89/0.99      ( k1_relat_1(sK2) = sK1 ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2241,c_28,c_29]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_776,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | v1_relat_1(X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1251,plain,
% 2.89/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | v1_relat_1(X0_50) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1632,plain,
% 2.89/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1251]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1,plain,
% 2.89/0.99      ( ~ v1_relat_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v2_funct_1(X0)
% 2.89/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_777,plain,
% 2.89/0.99      ( ~ v1_relat_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v2_funct_1(X0_50)
% 2.89/0.99      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1250,plain,
% 2.89/0.99      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 2.89/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1737,plain,
% 2.89/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top
% 2.89/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1632,c_1250]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_25,negated_conjecture,
% 2.89/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_819,plain,
% 2.89/0.99      ( ~ v1_relat_1(sK2)
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | ~ v2_funct_1(sK2)
% 2.89/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_777]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_822,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | v1_relat_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_776]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_8,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | v2_funct_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_772,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | v2_funct_1(X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_832,plain,
% 2.89/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | v2_funct_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_772]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1822,plain,
% 2.89/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_1737,c_27,c_25,c_24,c_819,c_822,c_832]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2809,plain,
% 2.89/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_2806,c_1822]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_21,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_763,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1264,plain,
% 2.89/0.99      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 2.89/0.99      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2365,plain,
% 2.89/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.89/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1264]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_853,plain,
% 2.89/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2555,plain,
% 2.89/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2365,c_27,c_26,c_25,c_24,c_853]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_12,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.89/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_771,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1256,plain,
% 2.89/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2886,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_2555,c_1256]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_30,plain,
% 2.89/0.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_31,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_834,plain,
% 2.89/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_836,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_834]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_782,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1501,plain,
% 2.89/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_782]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1559,plain,
% 2.89/0.99      ( X0_50 != X1_50
% 2.89/0.99      | X0_50 = k2_funct_2(X0_51,X2_50)
% 2.89/0.99      | k2_funct_2(X0_51,X2_50) != X1_50 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_784]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1663,plain,
% 2.89/0.99      ( X0_50 = k2_funct_2(X0_51,X1_50)
% 2.89/0.99      | X0_50 != k2_funct_1(X1_50)
% 2.89/0.99      | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1559]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1798,plain,
% 2.89/0.99      ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
% 2.89/0.99      | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
% 2.89/0.99      | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1663]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1800,plain,
% 2.89/0.99      ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 2.89/0.99      | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
% 2.89/0.99      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_780,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1799,plain,
% 2.89/0.99      ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_780]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1801,plain,
% 2.89/0.99      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1799]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_792,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,X0_52)
% 2.89/0.99      | m1_subset_1(X1_50,X1_52)
% 2.89/0.99      | X1_52 != X0_52
% 2.89/0.99      | X1_50 != X0_50 ),
% 2.89/0.99      theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1486,plain,
% 2.89/0.99      ( m1_subset_1(X0_50,X0_52)
% 2.89/0.99      | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 2.89/0.99      | X0_50 != k2_funct_2(X0_51,X1_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2138,plain,
% 2.89/0.99      ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | m1_subset_1(k2_funct_1(X0_50),X0_52)
% 2.89/0.99      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 2.89/0.99      | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1486]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2787,plain,
% 2.89/0.99      ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.89/0.99      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2138]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2788,plain,
% 2.89/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.89/0.99      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50)
% 2.89/0.99      | m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2790,plain,
% 2.89/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.89/0.99      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2)
% 2.89/0.99      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.89/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2788]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3813,plain,
% 2.89/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2886,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_836,
% 2.89/0.99                 c_853,c_1501,c_1800,c_1801,c_2790]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_20,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X3)
% 2.89/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_764,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(X1_50)
% 2.89/0.99      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1263,plain,
% 2.89/0.99      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 2.89/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | v1_funct_1(X1_50) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3230,plain,
% 2.89/0.99      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1263]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3361,plain,
% 2.89/0.99      ( v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3230,c_28]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3362,plain,
% 2.89/0.99      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.89/0.99      inference(renaming,[status(thm)],[c_3361]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3818,plain,
% 2.89/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.89/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3813,c_3362]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_835,plain,
% 2.89/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_771]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_15,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_768,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1259,plain,
% 2.89/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2325,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1267,c_1259]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_843,plain,
% 2.89/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.89/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.89/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_845,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.89/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_843]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2549,plain,
% 2.89/0.99      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2325,c_28,c_29,c_30,c_31,c_845]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2558,plain,
% 2.89/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_2555,c_2549]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2566,plain,
% 2.89/0.99      ( v1_funct_1(k2_funct_1(sK2)) ),
% 2.89/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2558]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2789,plain,
% 2.89/0.99      ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.89/0.99      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2787]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3792,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(k2_funct_1(X0_50))
% 2.89/0.99      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_764]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3795,plain,
% 2.89/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_3792]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4020,plain,
% 2.89/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3818,c_27,c_26,c_25,c_24,c_835,c_853,c_1501,c_1800,
% 2.89/0.99                 c_1801,c_2566,c_2789,c_3795]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_23,negated_conjecture,
% 2.89/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.89/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_761,negated_conjecture,
% 2.89/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.89/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1266,plain,
% 2.89/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.89/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2559,plain,
% 2.89/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.89/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_2555,c_1266]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4023,plain,
% 2.89/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.89/0.99      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_4020,c_2559]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4523,plain,
% 2.89/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.89/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_2809,c_4023]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_793,plain,
% 2.89/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.89/0.99      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 2.89/0.99      | X2_51 != X0_51
% 2.89/0.99      | X3_51 != X1_51
% 2.89/0.99      | X2_50 != X0_50
% 2.89/0.99      | X3_50 != X1_50 ),
% 2.89/0.99      theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2295,plain,
% 2.89/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.89/0.99      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 2.89/0.99      | X2_51 != X0_51
% 2.89/0.99      | X3_51 != X1_51
% 2.89/0.99      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 2.89/0.99      | k6_partfun1(X8_51) != X1_50 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_793]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3437,plain,
% 2.89/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 2.89/0.99      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 2.89/0.99      | X3_51 != X0_51
% 2.89/0.99      | X4_51 != X1_51
% 2.89/0.99      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 2.89/0.99      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2295]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4325,plain,
% 2.89/0.99      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 2.89/0.99      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 2.89/0.99      | X0_51 != X7_51
% 2.89/0.99      | X1_51 != X8_51
% 2.89/0.99      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 2.89/0.99      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_3437]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4327,plain,
% 2.89/0.99      ( X0_51 != X1_51
% 2.89/0.99      | X2_51 != X3_51
% 2.89/0.99      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
% 2.89/0.99      | k6_partfun1(X9_51) != k6_partfun1(X8_51)
% 2.89/0.99      | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
% 2.89/0.99      | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_4325]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4329,plain,
% 2.89/0.99      ( sK1 != sK1
% 2.89/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 2.89/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 2.89/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
% 2.89/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_4327]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3591,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.89/0.99      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_764]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3594,plain,
% 2.89/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_3591]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_785,plain,
% 2.89/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.89/0.99      theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2165,plain,
% 2.89/0.99      ( k2_relat_1(X0_50) != X0_51
% 2.89/0.99      | sK1 != X0_51
% 2.89/0.99      | sK1 = k2_relat_1(X0_50) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_785]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2166,plain,
% 2.89/0.99      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2165]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_6,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_773,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1254,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_5,plain,
% 2.89/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_774,plain,
% 2.89/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1253,plain,
% 2.89/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.89/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2074,plain,
% 2.89/0.99      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 2.89/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1254,c_1253]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2092,plain,
% 2.89/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2074]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_787,plain,
% 2.89/0.99      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 2.89/0.99      theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1519,plain,
% 2.89/0.99      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_787]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1987,plain,
% 2.89/0.99      ( sK1 != k2_relat_1(X0_50)
% 2.89/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1519]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1988,plain,
% 2.89/0.99      ( sK1 != k2_relat_1(sK2)
% 2.89/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1987]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1517,plain,
% 2.89/0.99      ( X0_50 != X1_50
% 2.89/0.99      | k6_partfun1(sK1) != X1_50
% 2.89/0.99      | k6_partfun1(sK1) = X0_50 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_784]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1599,plain,
% 2.89/0.99      ( X0_50 != k6_partfun1(X0_51)
% 2.89/0.99      | k6_partfun1(sK1) = X0_50
% 2.89/0.99      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1517]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1692,plain,
% 2.89/0.99      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 2.89/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 2.89/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1599]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1693,plain,
% 2.89/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 2.89/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.89/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1692]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_7,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | v2_funct_2(X0,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_11,plain,
% 2.89/0.99      ( ~ v2_funct_2(X0,X1)
% 2.89/0.99      | ~ v5_relat_1(X0,X1)
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | k2_relat_1(X0) = X1 ),
% 2.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_312,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v5_relat_1(X3,X4)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_relat_1(X3)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | X3 != X0
% 2.89/0.99      | X4 != X2
% 2.89/0.99      | k2_relat_1(X3) = X4 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_313,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v5_relat_1(X0,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k2_relat_1(X0) = X2 ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_312]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_317,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v5_relat_1(X0,X2)
% 2.89/0.99      | ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k2_relat_1(X0) = X2 ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_313,c_2]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_318,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v5_relat_1(X0,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k2_relat_1(X0) = X2 ),
% 2.89/0.99      inference(renaming,[status(thm)],[c_317]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3,plain,
% 2.89/0.99      ( v5_relat_1(X0,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_333,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | k2_relat_1(X0) = X2 ),
% 2.89/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_318,c_3]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_756,plain,
% 2.89/0.99      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.89/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | k2_relat_1(X0_50) = X1_51 ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_333]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_864,plain,
% 2.89/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.89/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | k2_relat_1(sK2) = sK1 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_756]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_0,plain,
% 2.89/0.99      ( ~ v1_relat_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v2_funct_1(X0)
% 2.89/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_778,plain,
% 2.89/0.99      ( ~ v1_relat_1(X0_50)
% 2.89/0.99      | ~ v1_funct_1(X0_50)
% 2.89/0.99      | ~ v2_funct_1(X0_50)
% 2.89/0.99      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.89/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_816,plain,
% 2.89/0.99      ( ~ v1_relat_1(sK2)
% 2.89/0.99      | ~ v1_funct_1(sK2)
% 2.89/0.99      | ~ v2_funct_1(sK2)
% 2.89/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_778]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_781,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_812,plain,
% 2.89/0.99      ( sK1 = sK1 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_781]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_799,plain,
% 2.89/0.99      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_787]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(contradiction,plain,
% 2.89/0.99      ( $false ),
% 2.89/0.99      inference(minisat,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_4695,c_4523,c_4329,c_3594,c_2789,c_2566,c_2166,c_2092,
% 2.89/0.99                 c_1988,c_1801,c_1800,c_1693,c_1501,c_864,c_853,c_835,
% 2.89/0.99                 c_832,c_822,c_816,c_812,c_799,c_31,c_24,c_25,c_26,c_27]) ).
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  ------                               Statistics
% 2.89/0.99  
% 2.89/0.99  ------ General
% 2.89/0.99  
% 2.89/0.99  abstr_ref_over_cycles:                  0
% 2.89/0.99  abstr_ref_under_cycles:                 0
% 2.89/0.99  gc_basic_clause_elim:                   0
% 2.89/0.99  forced_gc_time:                         0
% 2.89/0.99  parsing_time:                           0.01
% 2.89/0.99  unif_index_cands_time:                  0.
% 2.89/0.99  unif_index_add_time:                    0.
% 2.89/0.99  orderings_time:                         0.
% 2.89/0.99  out_proof_time:                         0.013
% 2.89/0.99  total_time:                             0.179
% 2.89/0.99  num_of_symbols:                         57
% 2.89/0.99  num_of_terms:                           4231
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing
% 2.89/0.99  
% 2.89/0.99  num_of_splits:                          0
% 2.89/0.99  num_of_split_atoms:                     0
% 2.89/0.99  num_of_reused_defs:                     0
% 2.89/0.99  num_eq_ax_congr_red:                    28
% 2.89/0.99  num_of_sem_filtered_clauses:            1
% 2.89/0.99  num_of_subtypes:                        4
% 2.89/0.99  monotx_restored_types:                  1
% 2.89/0.99  sat_num_of_epr_types:                   0
% 2.89/0.99  sat_num_of_non_cyclic_types:            0
% 2.89/0.99  sat_guarded_non_collapsed_types:        0
% 2.89/0.99  num_pure_diseq_elim:                    0
% 2.89/0.99  simp_replaced_by:                       0
% 2.89/0.99  res_preprocessed:                       133
% 2.89/0.99  prep_upred:                             0
% 2.89/0.99  prep_unflattend:                        8
% 2.89/0.99  smt_new_axioms:                         0
% 2.89/0.99  pred_elim_cands:                        7
% 2.89/0.99  pred_elim:                              2
% 2.89/0.99  pred_elim_cl:                           4
% 2.89/0.99  pred_elim_cycles:                       6
% 2.89/0.99  merged_defs:                            0
% 2.89/0.99  merged_defs_ncl:                        0
% 2.89/0.99  bin_hyper_res:                          0
% 2.89/0.99  prep_cycles:                            4
% 2.89/0.99  pred_elim_time:                         0.006
% 2.89/0.99  splitting_time:                         0.
% 2.89/0.99  sem_filter_time:                        0.
% 2.89/0.99  monotx_time:                            0.001
% 2.89/0.99  subtype_inf_time:                       0.001
% 2.89/0.99  
% 2.89/0.99  ------ Problem properties
% 2.89/0.99  
% 2.89/0.99  clauses:                                23
% 2.89/0.99  conjectures:                            5
% 2.89/0.99  epr:                                    3
% 2.89/0.99  horn:                                   23
% 2.89/0.99  ground:                                 5
% 2.89/0.99  unary:                                  8
% 2.89/0.99  binary:                                 3
% 2.89/0.99  lits:                                   67
% 2.89/0.99  lits_eq:                                7
% 2.89/0.99  fd_pure:                                0
% 2.89/0.99  fd_pseudo:                              0
% 2.89/0.99  fd_cond:                                0
% 2.89/0.99  fd_pseudo_cond:                         1
% 2.89/0.99  ac_symbols:                             0
% 2.89/0.99  
% 2.89/0.99  ------ Propositional Solver
% 2.89/0.99  
% 2.89/0.99  prop_solver_calls:                      29
% 2.89/0.99  prop_fast_solver_calls:                 1035
% 2.89/0.99  smt_solver_calls:                       0
% 2.89/0.99  smt_fast_solver_calls:                  0
% 2.89/0.99  prop_num_of_clauses:                    1338
% 2.89/0.99  prop_preprocess_simplified:             5296
% 2.89/0.99  prop_fo_subsumed:                       42
% 2.89/0.99  prop_solver_time:                       0.
% 2.89/0.99  smt_solver_time:                        0.
% 2.89/0.99  smt_fast_solver_time:                   0.
% 2.89/0.99  prop_fast_solver_time:                  0.
% 2.89/0.99  prop_unsat_core_time:                   0.
% 2.89/0.99  
% 2.89/0.99  ------ QBF
% 2.89/0.99  
% 2.89/0.99  qbf_q_res:                              0
% 2.89/0.99  qbf_num_tautologies:                    0
% 2.89/0.99  qbf_prep_cycles:                        0
% 2.89/0.99  
% 2.89/0.99  ------ BMC1
% 2.89/0.99  
% 2.89/0.99  bmc1_current_bound:                     -1
% 2.89/0.99  bmc1_last_solved_bound:                 -1
% 2.89/0.99  bmc1_unsat_core_size:                   -1
% 2.89/0.99  bmc1_unsat_core_parents_size:           -1
% 2.89/0.99  bmc1_merge_next_fun:                    0
% 2.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation
% 2.89/0.99  
% 2.89/0.99  inst_num_of_clauses:                    426
% 2.89/0.99  inst_num_in_passive:                    69
% 2.89/0.99  inst_num_in_active:                     271
% 2.89/0.99  inst_num_in_unprocessed:                85
% 2.89/0.99  inst_num_of_loops:                      296
% 2.89/0.99  inst_num_of_learning_restarts:          0
% 2.89/0.99  inst_num_moves_active_passive:          20
% 2.89/0.99  inst_lit_activity:                      0
% 2.89/0.99  inst_lit_activity_moves:                0
% 2.89/0.99  inst_num_tautologies:                   0
% 2.89/0.99  inst_num_prop_implied:                  0
% 2.89/0.99  inst_num_existing_simplified:           0
% 2.89/0.99  inst_num_eq_res_simplified:             0
% 2.89/0.99  inst_num_child_elim:                    0
% 2.89/0.99  inst_num_of_dismatching_blockings:      420
% 2.89/0.99  inst_num_of_non_proper_insts:           632
% 2.89/0.99  inst_num_of_duplicates:                 0
% 2.89/0.99  inst_inst_num_from_inst_to_res:         0
% 2.89/0.99  inst_dismatching_checking_time:         0.
% 2.89/0.99  
% 2.89/0.99  ------ Resolution
% 2.89/0.99  
% 2.89/0.99  res_num_of_clauses:                     0
% 2.89/0.99  res_num_in_passive:                     0
% 2.89/0.99  res_num_in_active:                      0
% 2.89/0.99  res_num_of_loops:                       137
% 2.89/0.99  res_forward_subset_subsumed:            94
% 2.89/0.99  res_backward_subset_subsumed:           4
% 2.89/0.99  res_forward_subsumed:                   0
% 2.89/0.99  res_backward_subsumed:                  0
% 2.89/0.99  res_forward_subsumption_resolution:     1
% 2.89/0.99  res_backward_subsumption_resolution:    0
% 2.89/0.99  res_clause_to_clause_subsumption:       177
% 2.89/0.99  res_orphan_elimination:                 0
% 2.89/0.99  res_tautology_del:                      82
% 2.89/0.99  res_num_eq_res_simplified:              0
% 2.89/0.99  res_num_sel_changes:                    0
% 2.89/0.99  res_moves_from_active_to_pass:          0
% 2.89/0.99  
% 2.89/0.99  ------ Superposition
% 2.89/0.99  
% 2.89/0.99  sup_time_total:                         0.
% 2.89/0.99  sup_time_generating:                    0.
% 2.89/0.99  sup_time_sim_full:                      0.
% 2.89/0.99  sup_time_sim_immed:                     0.
% 2.89/0.99  
% 2.89/0.99  sup_num_of_clauses:                     95
% 2.89/0.99  sup_num_in_active:                      49
% 2.89/0.99  sup_num_in_passive:                     46
% 2.89/0.99  sup_num_of_loops:                       58
% 2.89/0.99  sup_fw_superposition:                   54
% 2.89/0.99  sup_bw_superposition:                   24
% 2.89/0.99  sup_immediate_simplified:               12
% 2.89/0.99  sup_given_eliminated:                   0
% 2.89/0.99  comparisons_done:                       0
% 2.89/0.99  comparisons_avoided:                    0
% 2.89/0.99  
% 2.89/0.99  ------ Simplifications
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  sim_fw_subset_subsumed:                 1
% 2.89/0.99  sim_bw_subset_subsumed:                 2
% 2.89/0.99  sim_fw_subsumed:                        1
% 2.89/0.99  sim_bw_subsumed:                        0
% 2.89/0.99  sim_fw_subsumption_res:                 2
% 2.89/0.99  sim_bw_subsumption_res:                 0
% 2.89/0.99  sim_tautology_del:                      0
% 2.89/0.99  sim_eq_tautology_del:                   1
% 2.89/0.99  sim_eq_res_simp:                        0
% 2.89/0.99  sim_fw_demodulated:                     3
% 2.89/0.99  sim_bw_demodulated:                     9
% 2.89/0.99  sim_light_normalised:                   3
% 2.89/0.99  sim_joinable_taut:                      0
% 2.89/0.99  sim_joinable_simp:                      0
% 2.89/0.99  sim_ac_normalised:                      0
% 2.89/0.99  sim_smt_subsumption:                    0
% 2.89/0.99  
%------------------------------------------------------------------------------
