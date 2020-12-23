%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:21 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  218 (4360 expanded)
%              Number of clauses        :  135 (1275 expanded)
%              Number of leaves         :   20 ( 859 expanded)
%              Depth                    :   30
%              Number of atoms          :  691 (20296 expanded)
%              Number of equality atoms :  284 (1758 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f58,plain,
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

fof(f59,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f58])).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f89])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f89])).

fof(f97,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1439,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1423,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1430,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3342,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1430])).

cnf(c_6115,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_3342])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1420,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1424,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2975,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1424])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1432,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2406,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1420,c_1432])).

cnf(c_2980,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2975,c_2406])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_38,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3525,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_38])).

cnf(c_3526,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3525])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1431,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2391,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1420,c_1431])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_421,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_433,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_10])).

cnf(c_464,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_433])).

cnf(c_465,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_34,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_34])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_36,c_33])).

cnf(c_1416,plain,
    ( k2_relat_1(sK1) = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_1668,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_1760,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1416,c_33,c_1668])).

cnf(c_2393,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2391,c_1760])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( v2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_36,c_33])).

cnf(c_560,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_514])).

cnf(c_561,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relset_1(X0,X1,sK1) != X1 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK1,X0,X1)
    | k2_relset_1(X0,X1,sK1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_36])).

cnf(c_566,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK1) != X1 ),
    inference(renaming,[status(thm)],[c_565])).

cnf(c_1414,plain,
    ( k2_relset_1(X0,X1,sK1) != X1
    | v1_funct_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_2686,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_1414])).

cnf(c_40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1677,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relset_1(sK0,sK0,sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_1678,plain,
    ( k2_relset_1(sK0,sK0,sK1) != sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_2819,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2686,c_38,c_40,c_1678,c_2393])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1422,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4104,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_1422])).

cnf(c_37,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1680,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1681,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1680])).

cnf(c_1699,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1700,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_5325,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4104,c_37,c_40,c_1681,c_1700])).

cnf(c_5326,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5325])).

cnf(c_5336,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_5326])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_584,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_514])).

cnf(c_585,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_36])).

cnf(c_1413,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_2013,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1413,c_36,c_33,c_585,c_1699])).

cnf(c_5344,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5336,c_2013])).

cnf(c_5364,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5344,c_37])).

cnf(c_4103,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1422])).

cnf(c_4387,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_37])).

cnf(c_4388,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4387])).

cnf(c_4399,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_4388])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_598,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_514])).

cnf(c_599,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_601,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_36])).

cnf(c_1412,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1798,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1412,c_36,c_33,c_599,c_1699])).

cnf(c_1800,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1798,c_1760])).

cnf(c_4402,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4399,c_1800])).

cnf(c_4766,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4402,c_37,c_40,c_1681,c_1700])).

cnf(c_32,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1421,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_522,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_523,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_36,c_35,c_33])).

cnf(c_1588,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1421,c_525])).

cnf(c_4769,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4766,c_1588])).

cnf(c_5367,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5364,c_4769])).

cnf(c_5451,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_5367])).

cnf(c_6128,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6115,c_5451])).

cnf(c_6409,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6128,c_5367])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_612,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_514])).

cnf(c_613,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_615,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_36])).

cnf(c_1411,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_1793,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1411,c_36,c_33,c_613,c_1699])).

cnf(c_1795,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1793,c_1760])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1436,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1938,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1436])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_626,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_514])).

cnf(c_627,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_629,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_36])).

cnf(c_1410,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1789,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_36,c_33,c_627,c_1699])).

cnf(c_1939,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1938,c_1789])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1683,plain,
    ( ~ v1_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1684,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1683])).

cnf(c_2094,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1939,c_37,c_40,c_1684,c_1700])).

cnf(c_2095,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2094])).

cnf(c_6429,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6128,c_2095])).

cnf(c_6448,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6429])).

cnf(c_6515,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6409,c_6448])).

cnf(c_1768,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1769,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1768])).

cnf(c_1771,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_1687,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1690,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_1692,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_57,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_59,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6515,c_1771,c_1692,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:05:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.00/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.98  
% 3.00/0.98  ------  iProver source info
% 3.00/0.98  
% 3.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.98  git: non_committed_changes: false
% 3.00/0.98  git: last_make_outside_of_git: false
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     num_symb
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       true
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  ------ Parsing...
% 3.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.98  ------ Proving...
% 3.00/0.98  ------ Problem Properties 
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  clauses                                 31
% 3.00/0.98  conjectures                             4
% 3.00/0.98  EPR                                     2
% 3.00/0.98  Horn                                    27
% 3.00/0.98  unary                                   6
% 3.00/0.98  binary                                  9
% 3.00/0.98  lits                                    81
% 3.00/0.98  lits eq                                 27
% 3.00/0.98  fd_pure                                 0
% 3.00/0.98  fd_pseudo                               0
% 3.00/0.98  fd_cond                                 3
% 3.00/0.98  fd_pseudo_cond                          1
% 3.00/0.98  AC symbols                              0
% 3.00/0.98  
% 3.00/0.98  ------ Schedule dynamic 5 is on 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  Current options:
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     none
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       false
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ Proving...
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS status Theorem for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  fof(f1,axiom,(
% 3.00/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f60,plain,(
% 3.00/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f1])).
% 3.00/0.98  
% 3.00/0.98  fof(f16,axiom,(
% 3.00/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f23,plain,(
% 3.00/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.00/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.00/0.98  
% 3.00/0.98  fof(f86,plain,(
% 3.00/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f23])).
% 3.00/0.98  
% 3.00/0.98  fof(f12,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f39,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.00/0.98    inference(ennf_transformation,[],[f12])).
% 3.00/0.98  
% 3.00/0.98  fof(f40,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(flattening,[],[f39])).
% 3.00/0.98  
% 3.00/0.98  fof(f74,plain,(
% 3.00/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f40])).
% 3.00/0.98  
% 3.00/0.98  fof(f21,conjecture,(
% 3.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f22,negated_conjecture,(
% 3.00/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.00/0.98    inference(negated_conjecture,[],[f21])).
% 3.00/0.98  
% 3.00/0.98  fof(f53,plain,(
% 3.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.00/0.98    inference(ennf_transformation,[],[f22])).
% 3.00/0.98  
% 3.00/0.98  fof(f54,plain,(
% 3.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.00/0.98    inference(flattening,[],[f53])).
% 3.00/0.98  
% 3.00/0.98  fof(f58,plain,(
% 3.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f59,plain,(
% 3.00/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f58])).
% 3.00/0.98  
% 3.00/0.98  fof(f96,plain,(
% 3.00/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.00/0.98    inference(cnf_transformation,[],[f59])).
% 3.00/0.98  
% 3.00/0.98  fof(f14,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f43,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f14])).
% 3.00/0.98  
% 3.00/0.98  fof(f44,plain,(
% 3.00/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(flattening,[],[f43])).
% 3.00/0.98  
% 3.00/0.98  fof(f56,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(nnf_transformation,[],[f44])).
% 3.00/0.98  
% 3.00/0.98  fof(f78,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f56])).
% 3.00/0.98  
% 3.00/0.98  fof(f10,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f37,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f10])).
% 3.00/0.98  
% 3.00/0.98  fof(f72,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f37])).
% 3.00/0.98  
% 3.00/0.98  fof(f94,plain,(
% 3.00/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.00/0.98    inference(cnf_transformation,[],[f59])).
% 3.00/0.98  
% 3.00/0.98  fof(f11,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f38,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f11])).
% 3.00/0.98  
% 3.00/0.98  fof(f73,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f38])).
% 3.00/0.98  
% 3.00/0.98  fof(f13,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f41,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f13])).
% 3.00/0.98  
% 3.00/0.98  fof(f42,plain,(
% 3.00/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(flattening,[],[f41])).
% 3.00/0.98  
% 3.00/0.98  fof(f77,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f42])).
% 3.00/0.98  
% 3.00/0.98  fof(f9,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f24,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.00/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.00/0.98  
% 3.00/0.98  fof(f36,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f24])).
% 3.00/0.98  
% 3.00/0.98  fof(f71,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f36])).
% 3.00/0.98  
% 3.00/0.98  fof(f15,axiom,(
% 3.00/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f45,plain,(
% 3.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.00/0.98    inference(ennf_transformation,[],[f15])).
% 3.00/0.98  
% 3.00/0.98  fof(f46,plain,(
% 3.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(flattening,[],[f45])).
% 3.00/0.98  
% 3.00/0.98  fof(f57,plain,(
% 3.00/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f46])).
% 3.00/0.98  
% 3.00/0.98  fof(f84,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f57])).
% 3.00/0.98  
% 3.00/0.98  fof(f8,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f35,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/0.98    inference(ennf_transformation,[],[f8])).
% 3.00/0.98  
% 3.00/0.98  fof(f70,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f95,plain,(
% 3.00/0.98    v3_funct_2(sK1,sK0,sK0)),
% 3.00/0.98    inference(cnf_transformation,[],[f59])).
% 3.00/0.98  
% 3.00/0.98  fof(f93,plain,(
% 3.00/0.98    v1_funct_1(sK1)),
% 3.00/0.98    inference(cnf_transformation,[],[f59])).
% 3.00/0.98  
% 3.00/0.98  fof(f20,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f51,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.00/0.98    inference(ennf_transformation,[],[f20])).
% 3.00/0.98  
% 3.00/0.98  fof(f52,plain,(
% 3.00/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.00/0.98    inference(flattening,[],[f51])).
% 3.00/0.98  
% 3.00/0.98  fof(f92,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f52])).
% 3.00/0.98  
% 3.00/0.98  fof(f76,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f42])).
% 3.00/0.98  
% 3.00/0.98  fof(f17,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f47,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.00/0.98    inference(ennf_transformation,[],[f17])).
% 3.00/0.98  
% 3.00/0.98  fof(f48,plain,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.00/0.98    inference(flattening,[],[f47])).
% 3.00/0.98  
% 3.00/0.98  fof(f87,plain,(
% 3.00/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f48])).
% 3.00/0.98  
% 3.00/0.98  fof(f5,axiom,(
% 3.00/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f29,plain,(
% 3.00/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f5])).
% 3.00/0.98  
% 3.00/0.98  fof(f30,plain,(
% 3.00/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(flattening,[],[f29])).
% 3.00/0.98  
% 3.00/0.98  fof(f65,plain,(
% 3.00/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f30])).
% 3.00/0.98  
% 3.00/0.98  fof(f7,axiom,(
% 3.00/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f33,plain,(
% 3.00/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f7])).
% 3.00/0.98  
% 3.00/0.98  fof(f34,plain,(
% 3.00/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(flattening,[],[f33])).
% 3.00/0.98  
% 3.00/0.98  fof(f68,plain,(
% 3.00/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f34])).
% 3.00/0.98  
% 3.00/0.98  fof(f19,axiom,(
% 3.00/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f89,plain,(
% 3.00/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f19])).
% 3.00/0.98  
% 3.00/0.98  fof(f99,plain,(
% 3.00/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f68,f89])).
% 3.00/0.98  
% 3.00/0.98  fof(f69,plain,(
% 3.00/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f34])).
% 3.00/0.98  
% 3.00/0.98  fof(f98,plain,(
% 3.00/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f69,f89])).
% 3.00/0.98  
% 3.00/0.98  fof(f97,plain,(
% 3.00/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.00/0.98    inference(cnf_transformation,[],[f59])).
% 3.00/0.98  
% 3.00/0.98  fof(f18,axiom,(
% 3.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f49,plain,(
% 3.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.00/0.98    inference(ennf_transformation,[],[f18])).
% 3.00/0.98  
% 3.00/0.98  fof(f50,plain,(
% 3.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.00/0.98    inference(flattening,[],[f49])).
% 3.00/0.98  
% 3.00/0.98  fof(f88,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f50])).
% 3.00/0.98  
% 3.00/0.98  fof(f6,axiom,(
% 3.00/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f31,plain,(
% 3.00/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f6])).
% 3.00/0.98  
% 3.00/0.98  fof(f32,plain,(
% 3.00/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(flattening,[],[f31])).
% 3.00/0.98  
% 3.00/0.98  fof(f66,plain,(
% 3.00/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f32])).
% 3.00/0.98  
% 3.00/0.98  fof(f4,axiom,(
% 3.00/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f28,plain,(
% 3.00/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f4])).
% 3.00/0.98  
% 3.00/0.98  fof(f55,plain,(
% 3.00/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.00/0.98    inference(nnf_transformation,[],[f28])).
% 3.00/0.98  
% 3.00/0.98  fof(f62,plain,(
% 3.00/0.98    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f55])).
% 3.00/0.98  
% 3.00/0.98  fof(f67,plain,(
% 3.00/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f32])).
% 3.00/0.98  
% 3.00/0.98  fof(f64,plain,(
% 3.00/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f30])).
% 3.00/0.98  
% 3.00/0.98  cnf(c_0,plain,
% 3.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1439,plain,
% 3.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_26,plain,
% 3.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1423,plain,
% 3.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_14,plain,
% 3.00/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 3.00/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1430,plain,
% 3.00/0.98      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3342,plain,
% 3.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1423,c_1430]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_6115,plain,
% 3.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1439,c_3342]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_33,negated_conjecture,
% 3.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1420,plain,
% 3.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_23,plain,
% 3.00/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.00/0.98      | k1_xboole_0 = X2 ),
% 3.00/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1424,plain,
% 3.00/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.00/0.98      | k1_xboole_0 = X1
% 3.00/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2975,plain,
% 3.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.00/0.98      | sK0 = k1_xboole_0
% 3.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1420,c_1424]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_12,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1432,plain,
% 3.00/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2406,plain,
% 3.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1420,c_1432]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2980,plain,
% 3.00/0.98      ( k1_relat_1(sK1) = sK0
% 3.00/0.98      | sK0 = k1_xboole_0
% 3.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_2975,c_2406]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_35,negated_conjecture,
% 3.00/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_38,plain,
% 3.00/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3525,plain,
% 3.00/0.98      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_2980,c_38]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3526,plain,
% 3.00/0.98      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.00/0.98      inference(renaming,[status(thm)],[c_3525]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_13,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1431,plain,
% 3.00/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2391,plain,
% 3.00/0.98      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1420,c_1431]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_15,plain,
% 3.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/0.98      | v2_funct_2(X0,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | ~ v1_funct_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_11,plain,
% 3.00/0.98      ( v5_relat_1(X0,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_25,plain,
% 3.00/0.98      ( ~ v2_funct_2(X0,X1)
% 3.00/0.98      | ~ v5_relat_1(X0,X1)
% 3.00/0.98      | ~ v1_relat_1(X0)
% 3.00/0.98      | k2_relat_1(X0) = X1 ),
% 3.00/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_421,plain,
% 3.00/0.98      ( ~ v2_funct_2(X0,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/0.98      | ~ v1_relat_1(X0)
% 3.00/0.98      | k2_relat_1(X0) = X1 ),
% 3.00/0.98      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_10,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | v1_relat_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_433,plain,
% 3.00/0.98      ( ~ v2_funct_2(X0,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/0.98      | k2_relat_1(X0) = X1 ),
% 3.00/0.98      inference(forward_subsumption_resolution,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_421,c_10]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_464,plain,
% 3.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | X3 != X0
% 3.00/0.98      | X5 != X2
% 3.00/0.98      | k2_relat_1(X3) = X5 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_433]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_465,plain,
% 3.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | k2_relat_1(X0) = X2 ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_464]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_34,negated_conjecture,
% 3.00/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_493,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | k2_relat_1(X0) = X2
% 3.00/0.98      | sK1 != X0
% 3.00/0.98      | sK0 != X2
% 3.00/0.98      | sK0 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_465,c_34]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_494,plain,
% 3.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.98      | ~ v1_funct_1(sK1)
% 3.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_493]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_36,negated_conjecture,
% 3.00/0.98      ( v1_funct_1(sK1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_498,plain,
% 3.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_494,c_36,c_33]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1416,plain,
% 3.00/0.98      ( k2_relat_1(sK1) = sK0
% 3.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1668,plain,
% 3.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_498]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1760,plain,
% 3.00/0.98      ( k2_relat_1(sK1) = sK0 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_1416,c_33,c_1668]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2393,plain,
% 3.00/0.98      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_2391,c_1760]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_29,plain,
% 3.00/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/0.98      | ~ v2_funct_1(X0)
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.00/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_16,plain,
% 3.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | v2_funct_1(X0)
% 3.00/0.98      | ~ v1_funct_1(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_511,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | v2_funct_1(X0)
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | sK1 != X0
% 3.00/0.98      | sK0 != X2
% 3.00/0.98      | sK0 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_512,plain,
% 3.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.98      | v2_funct_1(sK1)
% 3.00/0.98      | ~ v1_funct_1(sK1) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_511]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_514,plain,
% 3.00/0.98      ( v2_funct_1(sK1) ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_512,c_36,c_33]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_560,plain,
% 3.00/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.00/0.98      | sK1 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_514]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_561,plain,
% 3.00/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/0.98      | ~ v1_funct_1(sK1)
% 3.00/0.98      | k2_relset_1(X0,X1,sK1) != X1 ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_560]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_565,plain,
% 3.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/0.98      | ~ v1_funct_2(sK1,X0,X1)
% 3.00/0.98      | k2_relset_1(X0,X1,sK1) != X1 ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_561,c_36]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_566,plain,
% 3.00/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/0.98      | k2_relset_1(X0,X1,sK1) != X1 ),
% 3.00/0.98      inference(renaming,[status(thm)],[c_565]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1414,plain,
% 3.00/0.98      ( k2_relset_1(X0,X1,sK1) != X1
% 3.00/0.98      | v1_funct_2(sK1,X0,X1) != iProver_top
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2686,plain,
% 3.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2393,c_1414]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_40,plain,
% 3.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1677,plain,
% 3.00/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.98      | k2_relset_1(sK0,sK0,sK1) != sK0 ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_566]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1678,plain,
% 3.00/0.98      ( k2_relset_1(sK0,sK0,sK1) != sK0
% 3.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2819,plain,
% 3.00/0.98      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_2686,c_38,c_40,c_1678,c_2393]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_27,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.00/0.98      | ~ v1_funct_1(X0)
% 3.00/0.98      | ~ v1_funct_1(X3)
% 3.00/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1422,plain,
% 3.00/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.00/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.00/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | v1_funct_1(X5) != iProver_top
% 3.00/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4104,plain,
% 3.00/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | v1_funct_1(X2) != iProver_top
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2819,c_1422]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_37,plain,
% 3.00/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.00/0.99      | ~ v1_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1680,plain,
% 3.00/0.99      ( v1_funct_1(k2_funct_1(sK1))
% 3.00/0.99      | ~ v1_funct_1(sK1)
% 3.00/0.99      | ~ v1_relat_1(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1681,plain,
% 3.00/0.99      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.00/0.99      | v1_funct_1(sK1) != iProver_top
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1680]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1699,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.99      | v1_relat_1(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1700,plain,
% 3.00/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.00/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5325,plain,
% 3.00/0.99      ( v1_funct_1(X2) != iProver_top
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4104,c_37,c_40,c_1681,c_1700]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5326,plain,
% 3.00/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_5325]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5336,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.00/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1420,c_5326]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_9,plain,
% 3.00/0.99      ( ~ v2_funct_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_584,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_514]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_585,plain,
% 3.00/0.99      ( ~ v1_funct_1(sK1)
% 3.00/0.99      | ~ v1_relat_1(sK1)
% 3.00/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_587,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK1)
% 3.00/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_585,c_36]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1413,plain,
% 3.00/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2013,plain,
% 3.00/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1413,c_36,c_33,c_585,c_1699]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5344,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.00/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_5336,c_2013]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5364,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_5344,c_37]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4103,plain,
% 3.00/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | v1_funct_1(X2) != iProver_top
% 3.00/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1420,c_1422]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4387,plain,
% 3.00/0.99      ( v1_funct_1(X2) != iProver_top
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4103,c_37]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4388,plain,
% 3.00/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.00/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_4387]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4399,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2819,c_4388]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_8,plain,
% 3.00/0.99      ( ~ v2_funct_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_598,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_514]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_599,plain,
% 3.00/0.99      ( ~ v1_funct_1(sK1)
% 3.00/0.99      | ~ v1_relat_1(sK1)
% 3.00/0.99      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_598]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_601,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK1)
% 3.00/0.99      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_599,c_36]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1412,plain,
% 3.00/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1798,plain,
% 3.00/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1412,c_36,c_33,c_599,c_1699]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1800,plain,
% 3.00/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_1798,c_1760]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4402,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.00/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_4399,c_1800]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4766,plain,
% 3.00/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4402,c_37,c_40,c_1681,c_1700]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_32,negated_conjecture,
% 3.00/0.99      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.00/0.99      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1421,plain,
% 3.00/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.00/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_28,plain,
% 3.00/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.00/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_522,plain,
% 3.00/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.00/0.99      | sK1 != X0
% 3.00/0.99      | sK0 != X1 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_523,plain,
% 3.00/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.00/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.00/0.99      | ~ v1_funct_1(sK1)
% 3.00/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_525,plain,
% 3.00/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_523,c_36,c_35,c_33]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1588,plain,
% 3.00/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.00/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_1421,c_525]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4769,plain,
% 3.00/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.00/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_4766,c_1588]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5367,plain,
% 3.00/0.99      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.00/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_5364,c_4769]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5451,plain,
% 3.00/0.99      ( sK0 = k1_xboole_0
% 3.00/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3526,c_5367]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6128,plain,
% 3.00/0.99      ( sK0 = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_6115,c_5451]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6409,plain,
% 3.00/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
% 3.00/0.99      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6128,c_5367]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7,plain,
% 3.00/0.99      ( ~ v2_funct_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_612,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_514]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_613,plain,
% 3.00/0.99      ( ~ v1_funct_1(sK1)
% 3.00/0.99      | ~ v1_relat_1(sK1)
% 3.00/0.99      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_612]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_615,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK1)
% 3.00/0.99      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_613,c_36]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1411,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1793,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1411,c_36,c_33,c_613,c_1699]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1795,plain,
% 3.00/0.99      ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_1793,c_1760]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3,plain,
% 3.00/0.99      ( ~ v1_relat_1(X0)
% 3.00/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.00/0.99      | k2_relat_1(X0) = k1_xboole_0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1436,plain,
% 3.00/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.00/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.00/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1938,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(sK1)) = k1_xboole_0
% 3.00/0.99      | sK0 != k1_xboole_0
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1795,c_1436]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6,plain,
% 3.00/0.99      ( ~ v2_funct_1(X0)
% 3.00/0.99      | ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_626,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_514]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_627,plain,
% 3.00/0.99      ( ~ v1_funct_1(sK1)
% 3.00/0.99      | ~ v1_relat_1(sK1)
% 3.00/0.99      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_629,plain,
% 3.00/0.99      ( ~ v1_relat_1(sK1)
% 3.00/0.99      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_627,c_36]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1410,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1789,plain,
% 3.00/0.99      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1410,c_36,c_33,c_627,c_1699]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1939,plain,
% 3.00/0.99      ( k1_relat_1(sK1) = k1_xboole_0
% 3.00/0.99      | sK0 != k1_xboole_0
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1938,c_1789]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5,plain,
% 3.00/0.99      ( ~ v1_funct_1(X0)
% 3.00/0.99      | ~ v1_relat_1(X0)
% 3.00/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1683,plain,
% 3.00/0.99      ( ~ v1_funct_1(sK1)
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK1))
% 3.00/0.99      | ~ v1_relat_1(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1684,plain,
% 3.00/0.99      ( v1_funct_1(sK1) != iProver_top
% 3.00/0.99      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 3.00/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1683]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2094,plain,
% 3.00/0.99      ( sK0 != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1939,c_37,c_40,c_1684,c_1700]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2095,plain,
% 3.00/0.99      ( k1_relat_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_2094]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6429,plain,
% 3.00/0.99      ( k1_relat_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6128,c_2095]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6448,plain,
% 3.00/0.99      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 3.00/0.99      inference(equality_resolution_simp,[status(thm)],[c_6429]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6515,plain,
% 3.00/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_6409,c_6448]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1768,plain,
% 3.00/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.00/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1769,plain,
% 3.00/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.00/0.99      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1768]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1771,plain,
% 3.00/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
% 3.00/0.99      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.00/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_1769]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1687,plain,
% 3.00/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1690,plain,
% 3.00/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1692,plain,
% 3.00/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_1690]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_57,plain,
% 3.00/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_59,plain,
% 3.00/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_57]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(contradiction,plain,
% 3.00/0.99      ( $false ),
% 3.00/0.99      inference(minisat,[status(thm)],[c_6515,c_1771,c_1692,c_59]) ).
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  ------                               Statistics
% 3.00/0.99  
% 3.00/0.99  ------ General
% 3.00/0.99  
% 3.00/0.99  abstr_ref_over_cycles:                  0
% 3.00/0.99  abstr_ref_under_cycles:                 0
% 3.00/0.99  gc_basic_clause_elim:                   0
% 3.00/0.99  forced_gc_time:                         0
% 3.00/0.99  parsing_time:                           0.01
% 3.00/0.99  unif_index_cands_time:                  0.
% 3.00/0.99  unif_index_add_time:                    0.
% 3.00/0.99  orderings_time:                         0.
% 3.00/0.99  out_proof_time:                         0.011
% 3.00/0.99  total_time:                             0.237
% 3.00/0.99  num_of_symbols:                         54
% 3.00/0.99  num_of_terms:                           6630
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing
% 3.00/0.99  
% 3.00/0.99  num_of_splits:                          0
% 3.00/0.99  num_of_split_atoms:                     0
% 3.00/0.99  num_of_reused_defs:                     0
% 3.00/0.99  num_eq_ax_congr_red:                    17
% 3.00/0.99  num_of_sem_filtered_clauses:            1
% 3.00/0.99  num_of_subtypes:                        0
% 3.00/0.99  monotx_restored_types:                  0
% 3.00/0.99  sat_num_of_epr_types:                   0
% 3.00/0.99  sat_num_of_non_cyclic_types:            0
% 3.00/0.99  sat_guarded_non_collapsed_types:        0
% 3.00/0.99  num_pure_diseq_elim:                    0
% 3.00/0.99  simp_replaced_by:                       0
% 3.00/0.99  res_preprocessed:                       166
% 3.00/0.99  prep_upred:                             0
% 3.00/0.99  prep_unflattend:                        20
% 3.00/0.99  smt_new_axioms:                         0
% 3.00/0.99  pred_elim_cands:                        5
% 3.00/0.99  pred_elim:                              4
% 3.00/0.99  pred_elim_cl:                           5
% 3.00/0.99  pred_elim_cycles:                       6
% 3.00/0.99  merged_defs:                            0
% 3.00/0.99  merged_defs_ncl:                        0
% 3.00/0.99  bin_hyper_res:                          0
% 3.00/0.99  prep_cycles:                            4
% 3.00/0.99  pred_elim_time:                         0.006
% 3.00/0.99  splitting_time:                         0.
% 3.00/0.99  sem_filter_time:                        0.
% 3.00/0.99  monotx_time:                            0.001
% 3.00/0.99  subtype_inf_time:                       0.
% 3.00/0.99  
% 3.00/0.99  ------ Problem properties
% 3.00/0.99  
% 3.00/0.99  clauses:                                31
% 3.00/0.99  conjectures:                            4
% 3.00/0.99  epr:                                    2
% 3.00/0.99  horn:                                   27
% 3.00/0.99  ground:                                 9
% 3.00/0.99  unary:                                  6
% 3.00/0.99  binary:                                 9
% 3.00/0.99  lits:                                   81
% 3.00/0.99  lits_eq:                                27
% 3.00/0.99  fd_pure:                                0
% 3.00/0.99  fd_pseudo:                              0
% 3.00/0.99  fd_cond:                                3
% 3.00/0.99  fd_pseudo_cond:                         1
% 3.00/0.99  ac_symbols:                             0
% 3.00/0.99  
% 3.00/0.99  ------ Propositional Solver
% 3.00/0.99  
% 3.00/0.99  prop_solver_calls:                      27
% 3.00/0.99  prop_fast_solver_calls:                 1228
% 3.00/0.99  smt_solver_calls:                       0
% 3.00/0.99  smt_fast_solver_calls:                  0
% 3.00/0.99  prop_num_of_clauses:                    2584
% 3.00/0.99  prop_preprocess_simplified:             7870
% 3.00/0.99  prop_fo_subsumed:                       41
% 3.00/0.99  prop_solver_time:                       0.
% 3.00/0.99  smt_solver_time:                        0.
% 3.00/0.99  smt_fast_solver_time:                   0.
% 3.00/0.99  prop_fast_solver_time:                  0.
% 3.00/0.99  prop_unsat_core_time:                   0.
% 3.00/0.99  
% 3.00/0.99  ------ QBF
% 3.00/0.99  
% 3.00/0.99  qbf_q_res:                              0
% 3.00/0.99  qbf_num_tautologies:                    0
% 3.00/0.99  qbf_prep_cycles:                        0
% 3.00/0.99  
% 3.00/0.99  ------ BMC1
% 3.00/0.99  
% 3.00/0.99  bmc1_current_bound:                     -1
% 3.00/0.99  bmc1_last_solved_bound:                 -1
% 3.00/0.99  bmc1_unsat_core_size:                   -1
% 3.00/0.99  bmc1_unsat_core_parents_size:           -1
% 3.00/0.99  bmc1_merge_next_fun:                    0
% 3.00/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation
% 3.00/0.99  
% 3.00/0.99  inst_num_of_clauses:                    822
% 3.00/0.99  inst_num_in_passive:                    66
% 3.00/0.99  inst_num_in_active:                     348
% 3.00/0.99  inst_num_in_unprocessed:                409
% 3.00/0.99  inst_num_of_loops:                      400
% 3.00/0.99  inst_num_of_learning_restarts:          0
% 3.00/0.99  inst_num_moves_active_passive:          49
% 3.00/0.99  inst_lit_activity:                      0
% 3.00/0.99  inst_lit_activity_moves:                0
% 3.00/0.99  inst_num_tautologies:                   0
% 3.00/0.99  inst_num_prop_implied:                  0
% 3.00/0.99  inst_num_existing_simplified:           0
% 3.00/0.99  inst_num_eq_res_simplified:             0
% 3.00/0.99  inst_num_child_elim:                    0
% 3.00/0.99  inst_num_of_dismatching_blockings:      225
% 3.00/0.99  inst_num_of_non_proper_insts:           701
% 3.00/0.99  inst_num_of_duplicates:                 0
% 3.00/0.99  inst_inst_num_from_inst_to_res:         0
% 3.00/0.99  inst_dismatching_checking_time:         0.
% 3.00/0.99  
% 3.00/0.99  ------ Resolution
% 3.00/0.99  
% 3.00/0.99  res_num_of_clauses:                     0
% 3.00/0.99  res_num_in_passive:                     0
% 3.00/0.99  res_num_in_active:                      0
% 3.00/0.99  res_num_of_loops:                       170
% 3.00/0.99  res_forward_subset_subsumed:            52
% 3.00/0.99  res_backward_subset_subsumed:           4
% 3.00/0.99  res_forward_subsumed:                   0
% 3.00/0.99  res_backward_subsumed:                  0
% 3.00/0.99  res_forward_subsumption_resolution:     2
% 3.00/0.99  res_backward_subsumption_resolution:    0
% 3.00/0.99  res_clause_to_clause_subsumption:       146
% 3.00/0.99  res_orphan_elimination:                 0
% 3.00/0.99  res_tautology_del:                      48
% 3.00/0.99  res_num_eq_res_simplified:              0
% 3.00/0.99  res_num_sel_changes:                    0
% 3.00/0.99  res_moves_from_active_to_pass:          0
% 3.00/0.99  
% 3.00/0.99  ------ Superposition
% 3.00/0.99  
% 3.00/0.99  sup_time_total:                         0.
% 3.00/0.99  sup_time_generating:                    0.
% 3.00/0.99  sup_time_sim_full:                      0.
% 3.00/0.99  sup_time_sim_immed:                     0.
% 3.00/0.99  
% 3.00/0.99  sup_num_of_clauses:                     68
% 3.00/0.99  sup_num_in_active:                      42
% 3.00/0.99  sup_num_in_passive:                     26
% 3.00/0.99  sup_num_of_loops:                       78
% 3.00/0.99  sup_fw_superposition:                   63
% 3.00/0.99  sup_bw_superposition:                   12
% 3.00/0.99  sup_immediate_simplified:               37
% 3.00/0.99  sup_given_eliminated:                   0
% 3.00/0.99  comparisons_done:                       0
% 3.00/0.99  comparisons_avoided:                    0
% 3.00/0.99  
% 3.00/0.99  ------ Simplifications
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  sim_fw_subset_subsumed:                 4
% 3.00/0.99  sim_bw_subset_subsumed:                 7
% 3.00/0.99  sim_fw_subsumed:                        1
% 3.00/0.99  sim_bw_subsumed:                        3
% 3.00/0.99  sim_fw_subsumption_res:                 1
% 3.00/0.99  sim_bw_subsumption_res:                 0
% 3.00/0.99  sim_tautology_del:                      2
% 3.00/0.99  sim_eq_tautology_del:                   8
% 3.00/0.99  sim_eq_res_simp:                        3
% 3.00/0.99  sim_fw_demodulated:                     6
% 3.00/0.99  sim_bw_demodulated:                     42
% 3.00/0.99  sim_light_normalised:                   16
% 3.00/0.99  sim_joinable_taut:                      0
% 3.00/0.99  sim_joinable_simp:                      0
% 3.00/0.99  sim_ac_normalised:                      0
% 3.00/0.99  sim_smt_subsumption:                    0
% 3.00/0.99  
%------------------------------------------------------------------------------
