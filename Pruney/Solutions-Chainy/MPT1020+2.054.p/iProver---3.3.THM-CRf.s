%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:15 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 388 expanded)
%              Number of clauses        :  114 ( 158 expanded)
%              Number of leaves         :   19 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  830 (2421 expanded)
%              Number of equality atoms :  264 ( 339 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k2_relat_1(X1) != k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k2_relat_1(X1) != k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_relat_1(X1) != k1_xboole_0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f71,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1052,plain,
    ( ~ v1_funct_2(X0_50,X0_49,X0_49)
    | ~ v3_funct_2(X0_50,X0_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1535,plain,
    ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_363,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_364,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_380,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_364,c_3])).

cnf(c_1036,plain,
    ( ~ v3_funct_2(X0_50,X0_49,X1_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) = X1_49 ),
    inference(subtyping,[status(esa)],[c_380])).

cnf(c_1551,plain,
    ( k2_relat_1(X0_50) = X0_49
    | v3_funct_2(X0_50,X1_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_4922,plain,
    ( k2_relat_1(k2_funct_2(X0_49,X0_50)) = X0_49
    | v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_50)) != iProver_top
    | v1_relat_1(k2_funct_2(X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1551])).

cnf(c_4924,plain,
    ( k2_relat_1(k2_funct_2(sK0,sK1)) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4922])).

cnf(c_1069,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
    | r2_relset_1(X2_49,X3_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    theory(equality)).

cnf(c_2036,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
    | r2_relset_1(X2_49,X3_49,sK2,X2_50)
    | X2_50 != X1_50
    | sK2 != X0_50
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2341,plain,
    ( ~ r2_relset_1(X0_49,X1_49,sK2,X0_50)
    | r2_relset_1(X2_49,X3_49,sK2,X1_50)
    | X1_50 != X0_50
    | sK2 != sK2
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    inference(instantiation,[status(thm)],[c_2036])).

cnf(c_2553,plain,
    ( r2_relset_1(X0_49,X1_49,sK2,X0_50)
    | ~ r2_relset_1(X2_49,X3_49,sK2,sK2)
    | X0_50 != sK2
    | sK2 != sK2
    | X0_49 != X2_49
    | X1_49 != X3_49 ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_4165,plain,
    ( r2_relset_1(X0_49,X1_49,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(X2_49,X3_49,sK2,sK2)
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | X0_49 != X2_49
    | X1_49 != X3_49 ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_4176,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4165])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_391,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v5_relat_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | X3 != X4
    | X0 != X5
    | k2_relat_1(X4) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_392,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v5_relat_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_416,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_392,c_3])).

cnf(c_1035,plain,
    ( ~ r2_relset_1(X0_49,X0_49,k1_partfun1(X0_49,X1_49,X1_49,X0_49,X0_50,X1_50),k6_partfun1(X0_49))
    | ~ v1_funct_2(X1_50,X1_49,X0_49)
    | ~ v1_funct_2(X0_50,X0_49,X1_49)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | ~ v1_relat_1(X1_50)
    | k2_relat_1(X1_50) = X0_49 ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_3484,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X0_49,X0_49,sK0,X0_50,sK2),k6_partfun1(sK0))
    | ~ v1_funct_2(X0_50,sK0,X0_49)
    | ~ v1_funct_2(sK2,X0_49,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_3486,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_1063,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1968,plain,
    ( k2_relat_1(X0_50) != X0_49
    | k2_relat_1(X0_50) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_3446,plain,
    ( k2_relat_1(k2_funct_2(sK0,sK1)) != X0_49
    | k2_relat_1(k2_funct_2(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_3447,plain,
    ( k2_relat_1(k2_funct_2(sK0,sK1)) != sK0
    | k2_relat_1(k2_funct_2(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3446])).

cnf(c_3444,plain,
    ( k2_relat_1(sK2) != X0_49
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_3445,plain,
    ( k2_relat_1(sK2) != sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_18])).

cnf(c_168,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_1037,plain,
    ( ~ r2_relset_1(X0_49,X0_49,k1_partfun1(X0_49,X1_49,X1_49,X0_49,X0_50,X1_50),k6_partfun1(X0_49))
    | ~ v1_funct_2(X1_50,X1_49,X0_49)
    | ~ v1_funct_2(X0_50,X0_49,X1_49)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_funct_1(X0_50) = X1_50
    | k2_relset_1(X0_49,X1_49,X0_50) != X1_49
    | k1_xboole_0 = X0_49
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_168])).

cnf(c_3106,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | k2_relset_1(sK0,sK0,sK1) != sK0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1058,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(k2_funct_2(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_2259,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_2261,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_2260,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(k2_funct_2(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1045,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1542,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1054,plain,
    ( r2_relset_1(X0_49,X1_49,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1533,plain,
    ( r2_relset_1(X0_49,X1_49,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_2218,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1533])).

cnf(c_2224,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2218])).

cnf(c_2207,plain,
    ( X0_49 != X1_49
    | X0_49 = k2_relat_1(X0_50)
    | k2_relat_1(X0_50) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_2208,plain,
    ( k2_relat_1(sK1) != sK0
    | sK0 = k2_relat_1(sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k2_relat_1(X1) != k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1056,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | X0_50 = X1_50
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(X1_50) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2023,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_funct_2(sK0,sK1))
    | k2_funct_2(sK0,sK1) = X0_50
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(k2_funct_2(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2025,plain,
    ( ~ v1_relat_1(k2_funct_2(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_funct_2(sK0,sK1) = sK1
    | k2_relat_1(k2_funct_2(sK0,sK1)) != k1_xboole_0
    | k2_relat_1(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_1798,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | k2_funct_2(sK0,sK1) != X1_50
    | sK2 != X0_50
    | sK0 != X0_49
    | sK0 != X1_49 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1929,plain,
    ( ~ r2_relset_1(X0_49,X1_49,sK2,X0_50)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | k2_funct_2(sK0,sK1) != X0_50
    | sK2 != sK2
    | sK0 != X0_49
    | sK0 != X1_49 ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_2010,plain,
    ( ~ r2_relset_1(X0_49,X1_49,sK2,k2_funct_1(sK1))
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | sK2 != sK2
    | sK0 != X0_49
    | sK0 != X1_49 ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_2013,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | sK2 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_1969,plain,
    ( k2_relat_1(sK1) != sK0
    | k2_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_1823,plain,
    ( X0_49 != X1_49
    | k2_relset_1(X2_49,X0_49,X0_50) != X1_49
    | k2_relset_1(X2_49,X0_49,X0_50) = X0_49 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1921,plain,
    ( X0_49 != k2_relat_1(X0_50)
    | k2_relset_1(X1_49,X0_49,X0_50) = X0_49
    | k2_relset_1(X1_49,X0_49,X0_50) != k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_1922,plain,
    ( k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1)
    | k2_relset_1(sK0,sK0,sK1) = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_1529,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_1896,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1529])).

cnf(c_1906,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1896])).

cnf(c_1862,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(sK2)
    | sK2 = X0_50
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1864,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | sK2 = sK1
    | k2_relat_1(sK1) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_1061,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1839,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1800,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | k2_funct_2(sK0,sK1) != sK1
    | sK2 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_1767,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_1130,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1048,plain,
    ( ~ v1_funct_2(X0_50,X0_49,X0_49)
    | ~ v3_funct_2(X0_50,X0_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_49,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1114,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1049,plain,
    ( ~ v1_funct_2(X0_50,X0_49,X0_49)
    | ~ v3_funct_2(X0_50,X0_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_49,X0_50)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1110,plain,
    ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_1112,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1051,plain,
    ( ~ v1_funct_2(X0_50,X0_49,X0_49)
    | ~ v3_funct_2(X0_50,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1104,plain,
    ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_1106,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_1101,plain,
    ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_1103,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1102,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1098,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1060,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1088,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_92,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_94,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_93,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4924,c_4176,c_3486,c_3447,c_3445,c_3106,c_2261,c_2260,c_2224,c_2208,c_2025,c_2013,c_1969,c_1922,c_1906,c_1864,c_1839,c_1800,c_1767,c_1130,c_1114,c_1112,c_1106,c_1103,c_1102,c_1098,c_1095,c_1088,c_94,c_93,c_20,c_21,c_22,c_24,c_25,c_33,c_26,c_32,c_27,c_31,c_28,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.27/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/1.00  
% 2.27/1.00  ------  iProver source info
% 2.27/1.00  
% 2.27/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.27/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/1.00  git: non_committed_changes: false
% 2.27/1.00  git: last_make_outside_of_git: false
% 2.27/1.00  
% 2.27/1.00  ------ 
% 2.27/1.00  
% 2.27/1.00  ------ Input Options
% 2.27/1.00  
% 2.27/1.00  --out_options                           all
% 2.27/1.00  --tptp_safe_out                         true
% 2.27/1.00  --problem_path                          ""
% 2.27/1.00  --include_path                          ""
% 2.27/1.00  --clausifier                            res/vclausify_rel
% 2.27/1.00  --clausifier_options                    --mode clausify
% 2.27/1.00  --stdin                                 false
% 2.27/1.00  --stats_out                             all
% 2.27/1.00  
% 2.27/1.00  ------ General Options
% 2.27/1.00  
% 2.27/1.00  --fof                                   false
% 2.27/1.00  --time_out_real                         305.
% 2.27/1.00  --time_out_virtual                      -1.
% 2.27/1.00  --symbol_type_check                     false
% 2.27/1.00  --clausify_out                          false
% 2.27/1.00  --sig_cnt_out                           false
% 2.27/1.00  --trig_cnt_out                          false
% 2.27/1.00  --trig_cnt_out_tolerance                1.
% 2.27/1.00  --trig_cnt_out_sk_spl                   false
% 2.27/1.00  --abstr_cl_out                          false
% 2.27/1.00  
% 2.27/1.00  ------ Global Options
% 2.27/1.00  
% 2.27/1.00  --schedule                              default
% 2.27/1.00  --add_important_lit                     false
% 2.27/1.00  --prop_solver_per_cl                    1000
% 2.27/1.00  --min_unsat_core                        false
% 2.27/1.00  --soft_assumptions                      false
% 2.27/1.00  --soft_lemma_size                       3
% 2.27/1.00  --prop_impl_unit_size                   0
% 2.27/1.00  --prop_impl_unit                        []
% 2.27/1.00  --share_sel_clauses                     true
% 2.27/1.00  --reset_solvers                         false
% 2.27/1.00  --bc_imp_inh                            [conj_cone]
% 2.27/1.00  --conj_cone_tolerance                   3.
% 2.27/1.00  --extra_neg_conj                        none
% 2.27/1.00  --large_theory_mode                     true
% 2.27/1.00  --prolific_symb_bound                   200
% 2.27/1.00  --lt_threshold                          2000
% 2.27/1.00  --clause_weak_htbl                      true
% 2.27/1.00  --gc_record_bc_elim                     false
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing Options
% 2.27/1.00  
% 2.27/1.00  --preprocessing_flag                    true
% 2.27/1.00  --time_out_prep_mult                    0.1
% 2.27/1.00  --splitting_mode                        input
% 2.27/1.00  --splitting_grd                         true
% 2.27/1.00  --splitting_cvd                         false
% 2.27/1.00  --splitting_cvd_svl                     false
% 2.27/1.00  --splitting_nvd                         32
% 2.27/1.00  --sub_typing                            true
% 2.27/1.00  --prep_gs_sim                           true
% 2.27/1.00  --prep_unflatten                        true
% 2.27/1.00  --prep_res_sim                          true
% 2.27/1.00  --prep_upred                            true
% 2.27/1.00  --prep_sem_filter                       exhaustive
% 2.27/1.00  --prep_sem_filter_out                   false
% 2.27/1.00  --pred_elim                             true
% 2.27/1.00  --res_sim_input                         true
% 2.27/1.00  --eq_ax_congr_red                       true
% 2.27/1.00  --pure_diseq_elim                       true
% 2.27/1.00  --brand_transform                       false
% 2.27/1.00  --non_eq_to_eq                          false
% 2.27/1.00  --prep_def_merge                        true
% 2.27/1.00  --prep_def_merge_prop_impl              false
% 2.27/1.00  --prep_def_merge_mbd                    true
% 2.27/1.00  --prep_def_merge_tr_red                 false
% 2.27/1.00  --prep_def_merge_tr_cl                  false
% 2.27/1.00  --smt_preprocessing                     true
% 2.27/1.00  --smt_ac_axioms                         fast
% 2.27/1.00  --preprocessed_out                      false
% 2.27/1.00  --preprocessed_stats                    false
% 2.27/1.00  
% 2.27/1.00  ------ Abstraction refinement Options
% 2.27/1.00  
% 2.27/1.00  --abstr_ref                             []
% 2.27/1.00  --abstr_ref_prep                        false
% 2.27/1.00  --abstr_ref_until_sat                   false
% 2.27/1.00  --abstr_ref_sig_restrict                funpre
% 2.27/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.00  --abstr_ref_under                       []
% 2.27/1.00  
% 2.27/1.00  ------ SAT Options
% 2.27/1.00  
% 2.27/1.00  --sat_mode                              false
% 2.27/1.00  --sat_fm_restart_options                ""
% 2.27/1.00  --sat_gr_def                            false
% 2.27/1.00  --sat_epr_types                         true
% 2.27/1.00  --sat_non_cyclic_types                  false
% 2.27/1.00  --sat_finite_models                     false
% 2.27/1.00  --sat_fm_lemmas                         false
% 2.27/1.00  --sat_fm_prep                           false
% 2.27/1.00  --sat_fm_uc_incr                        true
% 2.27/1.00  --sat_out_model                         small
% 2.27/1.00  --sat_out_clauses                       false
% 2.27/1.00  
% 2.27/1.00  ------ QBF Options
% 2.27/1.00  
% 2.27/1.00  --qbf_mode                              false
% 2.27/1.00  --qbf_elim_univ                         false
% 2.27/1.00  --qbf_dom_inst                          none
% 2.27/1.00  --qbf_dom_pre_inst                      false
% 2.27/1.00  --qbf_sk_in                             false
% 2.27/1.00  --qbf_pred_elim                         true
% 2.27/1.00  --qbf_split                             512
% 2.27/1.00  
% 2.27/1.00  ------ BMC1 Options
% 2.27/1.00  
% 2.27/1.00  --bmc1_incremental                      false
% 2.27/1.00  --bmc1_axioms                           reachable_all
% 2.27/1.00  --bmc1_min_bound                        0
% 2.27/1.00  --bmc1_max_bound                        -1
% 2.27/1.00  --bmc1_max_bound_default                -1
% 2.27/1.00  --bmc1_symbol_reachability              true
% 2.27/1.00  --bmc1_property_lemmas                  false
% 2.27/1.00  --bmc1_k_induction                      false
% 2.27/1.00  --bmc1_non_equiv_states                 false
% 2.27/1.00  --bmc1_deadlock                         false
% 2.27/1.00  --bmc1_ucm                              false
% 2.27/1.00  --bmc1_add_unsat_core                   none
% 2.27/1.00  --bmc1_unsat_core_children              false
% 2.27/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.00  --bmc1_out_stat                         full
% 2.27/1.00  --bmc1_ground_init                      false
% 2.27/1.00  --bmc1_pre_inst_next_state              false
% 2.27/1.00  --bmc1_pre_inst_state                   false
% 2.27/1.00  --bmc1_pre_inst_reach_state             false
% 2.27/1.00  --bmc1_out_unsat_core                   false
% 2.27/1.00  --bmc1_aig_witness_out                  false
% 2.27/1.00  --bmc1_verbose                          false
% 2.27/1.00  --bmc1_dump_clauses_tptp                false
% 2.27/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.00  --bmc1_dump_file                        -
% 2.27/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.00  --bmc1_ucm_extend_mode                  1
% 2.27/1.00  --bmc1_ucm_init_mode                    2
% 2.27/1.00  --bmc1_ucm_cone_mode                    none
% 2.27/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.00  --bmc1_ucm_relax_model                  4
% 2.27/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.00  --bmc1_ucm_layered_model                none
% 2.27/1.00  --bmc1_ucm_max_lemma_size               10
% 2.27/1.00  
% 2.27/1.00  ------ AIG Options
% 2.27/1.00  
% 2.27/1.00  --aig_mode                              false
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation Options
% 2.27/1.00  
% 2.27/1.00  --instantiation_flag                    true
% 2.27/1.00  --inst_sos_flag                         false
% 2.27/1.00  --inst_sos_phase                        true
% 2.27/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel_side                     num_symb
% 2.27/1.00  --inst_solver_per_active                1400
% 2.27/1.00  --inst_solver_calls_frac                1.
% 2.27/1.00  --inst_passive_queue_type               priority_queues
% 2.27/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.00  --inst_passive_queues_freq              [25;2]
% 2.27/1.00  --inst_dismatching                      true
% 2.27/1.00  --inst_eager_unprocessed_to_passive     true
% 2.27/1.00  --inst_prop_sim_given                   true
% 2.27/1.00  --inst_prop_sim_new                     false
% 2.27/1.00  --inst_subs_new                         false
% 2.27/1.00  --inst_eq_res_simp                      false
% 2.27/1.00  --inst_subs_given                       false
% 2.27/1.00  --inst_orphan_elimination               true
% 2.27/1.00  --inst_learning_loop_flag               true
% 2.27/1.00  --inst_learning_start                   3000
% 2.27/1.00  --inst_learning_factor                  2
% 2.27/1.00  --inst_start_prop_sim_after_learn       3
% 2.27/1.00  --inst_sel_renew                        solver
% 2.27/1.00  --inst_lit_activity_flag                true
% 2.27/1.00  --inst_restr_to_given                   false
% 2.27/1.00  --inst_activity_threshold               500
% 2.27/1.00  --inst_out_proof                        true
% 2.27/1.00  
% 2.27/1.00  ------ Resolution Options
% 2.27/1.00  
% 2.27/1.00  --resolution_flag                       true
% 2.27/1.00  --res_lit_sel                           adaptive
% 2.27/1.00  --res_lit_sel_side                      none
% 2.27/1.00  --res_ordering                          kbo
% 2.27/1.00  --res_to_prop_solver                    active
% 2.27/1.00  --res_prop_simpl_new                    false
% 2.27/1.00  --res_prop_simpl_given                  true
% 2.27/1.00  --res_passive_queue_type                priority_queues
% 2.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.00  --res_passive_queues_freq               [15;5]
% 2.27/1.00  --res_forward_subs                      full
% 2.27/1.00  --res_backward_subs                     full
% 2.27/1.00  --res_forward_subs_resolution           true
% 2.27/1.00  --res_backward_subs_resolution          true
% 2.27/1.00  --res_orphan_elimination                true
% 2.27/1.00  --res_time_limit                        2.
% 2.27/1.00  --res_out_proof                         true
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Options
% 2.27/1.00  
% 2.27/1.00  --superposition_flag                    true
% 2.27/1.00  --sup_passive_queue_type                priority_queues
% 2.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.00  --demod_completeness_check              fast
% 2.27/1.00  --demod_use_ground                      true
% 2.27/1.00  --sup_to_prop_solver                    passive
% 2.27/1.00  --sup_prop_simpl_new                    true
% 2.27/1.00  --sup_prop_simpl_given                  true
% 2.27/1.00  --sup_fun_splitting                     false
% 2.27/1.00  --sup_smt_interval                      50000
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Simplification Setup
% 2.27/1.00  
% 2.27/1.00  --sup_indices_passive                   []
% 2.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_full_bw                           [BwDemod]
% 2.27/1.00  --sup_immed_triv                        [TrivRules]
% 2.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_immed_bw_main                     []
% 2.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  
% 2.27/1.00  ------ Combination Options
% 2.27/1.00  
% 2.27/1.00  --comb_res_mult                         3
% 2.27/1.00  --comb_sup_mult                         2
% 2.27/1.00  --comb_inst_mult                        10
% 2.27/1.00  
% 2.27/1.00  ------ Debug Options
% 2.27/1.00  
% 2.27/1.00  --dbg_backtrace                         false
% 2.27/1.00  --dbg_dump_prop_clauses                 false
% 2.27/1.00  --dbg_dump_prop_clauses_file            -
% 2.27/1.00  --dbg_out_stat                          false
% 2.27/1.00  ------ Parsing...
% 2.27/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.00  ------ Proving...
% 2.27/1.00  ------ Problem Properties 
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  clauses                                 24
% 2.27/1.00  conjectures                             10
% 2.27/1.00  EPR                                     6
% 2.27/1.00  Horn                                    23
% 2.27/1.00  unary                                   11
% 2.27/1.00  binary                                  2
% 2.27/1.00  lits                                    77
% 2.27/1.00  lits eq                                 12
% 2.27/1.00  fd_pure                                 0
% 2.27/1.00  fd_pseudo                               0
% 2.27/1.00  fd_cond                                 0
% 2.27/1.00  fd_pseudo_cond                          5
% 2.27/1.00  AC symbols                              0
% 2.27/1.00  
% 2.27/1.00  ------ Schedule dynamic 5 is on 
% 2.27/1.00  
% 2.27/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  ------ 
% 2.27/1.00  Current options:
% 2.27/1.00  ------ 
% 2.27/1.00  
% 2.27/1.00  ------ Input Options
% 2.27/1.00  
% 2.27/1.00  --out_options                           all
% 2.27/1.00  --tptp_safe_out                         true
% 2.27/1.00  --problem_path                          ""
% 2.27/1.00  --include_path                          ""
% 2.27/1.00  --clausifier                            res/vclausify_rel
% 2.27/1.00  --clausifier_options                    --mode clausify
% 2.27/1.00  --stdin                                 false
% 2.27/1.00  --stats_out                             all
% 2.27/1.00  
% 2.27/1.00  ------ General Options
% 2.27/1.00  
% 2.27/1.00  --fof                                   false
% 2.27/1.00  --time_out_real                         305.
% 2.27/1.00  --time_out_virtual                      -1.
% 2.27/1.00  --symbol_type_check                     false
% 2.27/1.00  --clausify_out                          false
% 2.27/1.00  --sig_cnt_out                           false
% 2.27/1.00  --trig_cnt_out                          false
% 2.27/1.00  --trig_cnt_out_tolerance                1.
% 2.27/1.00  --trig_cnt_out_sk_spl                   false
% 2.27/1.00  --abstr_cl_out                          false
% 2.27/1.00  
% 2.27/1.00  ------ Global Options
% 2.27/1.00  
% 2.27/1.00  --schedule                              default
% 2.27/1.00  --add_important_lit                     false
% 2.27/1.00  --prop_solver_per_cl                    1000
% 2.27/1.00  --min_unsat_core                        false
% 2.27/1.00  --soft_assumptions                      false
% 2.27/1.00  --soft_lemma_size                       3
% 2.27/1.00  --prop_impl_unit_size                   0
% 2.27/1.00  --prop_impl_unit                        []
% 2.27/1.00  --share_sel_clauses                     true
% 2.27/1.00  --reset_solvers                         false
% 2.27/1.00  --bc_imp_inh                            [conj_cone]
% 2.27/1.00  --conj_cone_tolerance                   3.
% 2.27/1.00  --extra_neg_conj                        none
% 2.27/1.00  --large_theory_mode                     true
% 2.27/1.00  --prolific_symb_bound                   200
% 2.27/1.00  --lt_threshold                          2000
% 2.27/1.00  --clause_weak_htbl                      true
% 2.27/1.00  --gc_record_bc_elim                     false
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing Options
% 2.27/1.00  
% 2.27/1.00  --preprocessing_flag                    true
% 2.27/1.00  --time_out_prep_mult                    0.1
% 2.27/1.00  --splitting_mode                        input
% 2.27/1.00  --splitting_grd                         true
% 2.27/1.00  --splitting_cvd                         false
% 2.27/1.00  --splitting_cvd_svl                     false
% 2.27/1.00  --splitting_nvd                         32
% 2.27/1.00  --sub_typing                            true
% 2.27/1.00  --prep_gs_sim                           true
% 2.27/1.00  --prep_unflatten                        true
% 2.27/1.00  --prep_res_sim                          true
% 2.27/1.00  --prep_upred                            true
% 2.27/1.00  --prep_sem_filter                       exhaustive
% 2.27/1.00  --prep_sem_filter_out                   false
% 2.27/1.00  --pred_elim                             true
% 2.27/1.00  --res_sim_input                         true
% 2.27/1.00  --eq_ax_congr_red                       true
% 2.27/1.00  --pure_diseq_elim                       true
% 2.27/1.00  --brand_transform                       false
% 2.27/1.00  --non_eq_to_eq                          false
% 2.27/1.00  --prep_def_merge                        true
% 2.27/1.00  --prep_def_merge_prop_impl              false
% 2.27/1.00  --prep_def_merge_mbd                    true
% 2.27/1.00  --prep_def_merge_tr_red                 false
% 2.27/1.00  --prep_def_merge_tr_cl                  false
% 2.27/1.00  --smt_preprocessing                     true
% 2.27/1.00  --smt_ac_axioms                         fast
% 2.27/1.00  --preprocessed_out                      false
% 2.27/1.00  --preprocessed_stats                    false
% 2.27/1.00  
% 2.27/1.00  ------ Abstraction refinement Options
% 2.27/1.00  
% 2.27/1.00  --abstr_ref                             []
% 2.27/1.00  --abstr_ref_prep                        false
% 2.27/1.00  --abstr_ref_until_sat                   false
% 2.27/1.00  --abstr_ref_sig_restrict                funpre
% 2.27/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.00  --abstr_ref_under                       []
% 2.27/1.00  
% 2.27/1.00  ------ SAT Options
% 2.27/1.00  
% 2.27/1.00  --sat_mode                              false
% 2.27/1.00  --sat_fm_restart_options                ""
% 2.27/1.00  --sat_gr_def                            false
% 2.27/1.00  --sat_epr_types                         true
% 2.27/1.00  --sat_non_cyclic_types                  false
% 2.27/1.00  --sat_finite_models                     false
% 2.27/1.00  --sat_fm_lemmas                         false
% 2.27/1.00  --sat_fm_prep                           false
% 2.27/1.00  --sat_fm_uc_incr                        true
% 2.27/1.00  --sat_out_model                         small
% 2.27/1.00  --sat_out_clauses                       false
% 2.27/1.00  
% 2.27/1.00  ------ QBF Options
% 2.27/1.00  
% 2.27/1.00  --qbf_mode                              false
% 2.27/1.00  --qbf_elim_univ                         false
% 2.27/1.00  --qbf_dom_inst                          none
% 2.27/1.00  --qbf_dom_pre_inst                      false
% 2.27/1.00  --qbf_sk_in                             false
% 2.27/1.00  --qbf_pred_elim                         true
% 2.27/1.00  --qbf_split                             512
% 2.27/1.00  
% 2.27/1.00  ------ BMC1 Options
% 2.27/1.00  
% 2.27/1.00  --bmc1_incremental                      false
% 2.27/1.00  --bmc1_axioms                           reachable_all
% 2.27/1.00  --bmc1_min_bound                        0
% 2.27/1.00  --bmc1_max_bound                        -1
% 2.27/1.00  --bmc1_max_bound_default                -1
% 2.27/1.00  --bmc1_symbol_reachability              true
% 2.27/1.00  --bmc1_property_lemmas                  false
% 2.27/1.00  --bmc1_k_induction                      false
% 2.27/1.00  --bmc1_non_equiv_states                 false
% 2.27/1.00  --bmc1_deadlock                         false
% 2.27/1.00  --bmc1_ucm                              false
% 2.27/1.00  --bmc1_add_unsat_core                   none
% 2.27/1.00  --bmc1_unsat_core_children              false
% 2.27/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.00  --bmc1_out_stat                         full
% 2.27/1.00  --bmc1_ground_init                      false
% 2.27/1.00  --bmc1_pre_inst_next_state              false
% 2.27/1.00  --bmc1_pre_inst_state                   false
% 2.27/1.00  --bmc1_pre_inst_reach_state             false
% 2.27/1.00  --bmc1_out_unsat_core                   false
% 2.27/1.00  --bmc1_aig_witness_out                  false
% 2.27/1.00  --bmc1_verbose                          false
% 2.27/1.00  --bmc1_dump_clauses_tptp                false
% 2.27/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.00  --bmc1_dump_file                        -
% 2.27/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.00  --bmc1_ucm_extend_mode                  1
% 2.27/1.00  --bmc1_ucm_init_mode                    2
% 2.27/1.00  --bmc1_ucm_cone_mode                    none
% 2.27/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.00  --bmc1_ucm_relax_model                  4
% 2.27/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.00  --bmc1_ucm_layered_model                none
% 2.27/1.00  --bmc1_ucm_max_lemma_size               10
% 2.27/1.00  
% 2.27/1.00  ------ AIG Options
% 2.27/1.00  
% 2.27/1.00  --aig_mode                              false
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation Options
% 2.27/1.00  
% 2.27/1.00  --instantiation_flag                    true
% 2.27/1.00  --inst_sos_flag                         false
% 2.27/1.00  --inst_sos_phase                        true
% 2.27/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel_side                     none
% 2.27/1.00  --inst_solver_per_active                1400
% 2.27/1.00  --inst_solver_calls_frac                1.
% 2.27/1.00  --inst_passive_queue_type               priority_queues
% 2.27/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.00  --inst_passive_queues_freq              [25;2]
% 2.27/1.00  --inst_dismatching                      true
% 2.27/1.00  --inst_eager_unprocessed_to_passive     true
% 2.27/1.00  --inst_prop_sim_given                   true
% 2.27/1.00  --inst_prop_sim_new                     false
% 2.27/1.00  --inst_subs_new                         false
% 2.27/1.00  --inst_eq_res_simp                      false
% 2.27/1.00  --inst_subs_given                       false
% 2.27/1.00  --inst_orphan_elimination               true
% 2.27/1.00  --inst_learning_loop_flag               true
% 2.27/1.00  --inst_learning_start                   3000
% 2.27/1.00  --inst_learning_factor                  2
% 2.27/1.00  --inst_start_prop_sim_after_learn       3
% 2.27/1.00  --inst_sel_renew                        solver
% 2.27/1.00  --inst_lit_activity_flag                true
% 2.27/1.00  --inst_restr_to_given                   false
% 2.27/1.00  --inst_activity_threshold               500
% 2.27/1.00  --inst_out_proof                        true
% 2.27/1.00  
% 2.27/1.00  ------ Resolution Options
% 2.27/1.00  
% 2.27/1.00  --resolution_flag                       false
% 2.27/1.00  --res_lit_sel                           adaptive
% 2.27/1.00  --res_lit_sel_side                      none
% 2.27/1.00  --res_ordering                          kbo
% 2.27/1.00  --res_to_prop_solver                    active
% 2.27/1.00  --res_prop_simpl_new                    false
% 2.27/1.00  --res_prop_simpl_given                  true
% 2.27/1.00  --res_passive_queue_type                priority_queues
% 2.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.00  --res_passive_queues_freq               [15;5]
% 2.27/1.00  --res_forward_subs                      full
% 2.27/1.00  --res_backward_subs                     full
% 2.27/1.00  --res_forward_subs_resolution           true
% 2.27/1.00  --res_backward_subs_resolution          true
% 2.27/1.00  --res_orphan_elimination                true
% 2.27/1.00  --res_time_limit                        2.
% 2.27/1.00  --res_out_proof                         true
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Options
% 2.27/1.00  
% 2.27/1.00  --superposition_flag                    true
% 2.27/1.00  --sup_passive_queue_type                priority_queues
% 2.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.00  --demod_completeness_check              fast
% 2.27/1.00  --demod_use_ground                      true
% 2.27/1.00  --sup_to_prop_solver                    passive
% 2.27/1.00  --sup_prop_simpl_new                    true
% 2.27/1.00  --sup_prop_simpl_given                  true
% 2.27/1.00  --sup_fun_splitting                     false
% 2.27/1.00  --sup_smt_interval                      50000
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Simplification Setup
% 2.27/1.00  
% 2.27/1.00  --sup_indices_passive                   []
% 2.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_full_bw                           [BwDemod]
% 2.27/1.00  --sup_immed_triv                        [TrivRules]
% 2.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_immed_bw_main                     []
% 2.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  
% 2.27/1.00  ------ Combination Options
% 2.27/1.00  
% 2.27/1.00  --comb_res_mult                         3
% 2.27/1.00  --comb_sup_mult                         2
% 2.27/1.00  --comb_inst_mult                        10
% 2.27/1.00  
% 2.27/1.00  ------ Debug Options
% 2.27/1.00  
% 2.27/1.00  --dbg_backtrace                         false
% 2.27/1.00  --dbg_dump_prop_clauses                 false
% 2.27/1.00  --dbg_dump_prop_clauses_file            -
% 2.27/1.00  --dbg_out_stat                          false
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  ------ Proving...
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS status Theorem for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  fof(f9,axiom,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f27,plain,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.27/1.00    inference(ennf_transformation,[],[f9])).
% 2.27/1.00  
% 2.27/1.00  fof(f28,plain,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.27/1.00    inference(flattening,[],[f27])).
% 2.27/1.00  
% 2.27/1.00  fof(f57,plain,(
% 2.27/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f28])).
% 2.27/1.00  
% 2.27/1.00  fof(f7,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f23,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(ennf_transformation,[],[f7])).
% 2.27/1.00  
% 2.27/1.00  fof(f24,plain,(
% 2.27/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(flattening,[],[f23])).
% 2.27/1.00  
% 2.27/1.00  fof(f51,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f24])).
% 2.27/1.00  
% 2.27/1.00  fof(f8,axiom,(
% 2.27/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f25,plain,(
% 2.27/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.27/1.00    inference(ennf_transformation,[],[f8])).
% 2.27/1.00  
% 2.27/1.00  fof(f26,plain,(
% 2.27/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/1.00    inference(flattening,[],[f25])).
% 2.27/1.00  
% 2.27/1.00  fof(f38,plain,(
% 2.27/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/1.00    inference(nnf_transformation,[],[f26])).
% 2.27/1.00  
% 2.27/1.00  fof(f52,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f38])).
% 2.27/1.00  
% 2.27/1.00  fof(f4,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f15,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.27/1.00    inference(pure_predicate_removal,[],[f4])).
% 2.27/1.00  
% 2.27/1.00  fof(f19,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(ennf_transformation,[],[f15])).
% 2.27/1.00  
% 2.27/1.00  fof(f45,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f19])).
% 2.27/1.00  
% 2.27/1.00  fof(f11,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f31,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.27/1.00    inference(ennf_transformation,[],[f11])).
% 2.27/1.00  
% 2.27/1.00  fof(f32,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.27/1.00    inference(flattening,[],[f31])).
% 2.27/1.00  
% 2.27/1.00  fof(f60,plain,(
% 2.27/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f32])).
% 2.27/1.00  
% 2.27/1.00  fof(f12,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f33,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.27/1.00    inference(ennf_transformation,[],[f12])).
% 2.27/1.00  
% 2.27/1.00  fof(f34,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.27/1.00    inference(flattening,[],[f33])).
% 2.27/1.00  
% 2.27/1.00  fof(f61,plain,(
% 2.27/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f34])).
% 2.27/1.00  
% 2.27/1.00  fof(f59,plain,(
% 2.27/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f32])).
% 2.27/1.00  
% 2.27/1.00  fof(f1,axiom,(
% 2.27/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f16,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/1.00    inference(ennf_transformation,[],[f1])).
% 2.27/1.00  
% 2.27/1.00  fof(f42,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f16])).
% 2.27/1.00  
% 2.27/1.00  fof(f13,conjecture,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f14,negated_conjecture,(
% 2.27/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.27/1.00    inference(negated_conjecture,[],[f13])).
% 2.27/1.00  
% 2.27/1.00  fof(f35,plain,(
% 2.27/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.27/1.00    inference(ennf_transformation,[],[f14])).
% 2.27/1.00  
% 2.27/1.00  fof(f36,plain,(
% 2.27/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.27/1.00    inference(flattening,[],[f35])).
% 2.27/1.00  
% 2.27/1.00  fof(f40,plain,(
% 2.27/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f39,plain,(
% 2.27/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f41,plain,(
% 2.27/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f69,plain,(
% 2.27/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f6,axiom,(
% 2.27/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f21,plain,(
% 2.27/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.27/1.00    inference(ennf_transformation,[],[f6])).
% 2.27/1.00  
% 2.27/1.00  fof(f22,plain,(
% 2.27/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(flattening,[],[f21])).
% 2.27/1.00  
% 2.27/1.00  fof(f37,plain,(
% 2.27/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(nnf_transformation,[],[f22])).
% 2.27/1.00  
% 2.27/1.00  fof(f48,plain,(
% 2.27/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f37])).
% 2.27/1.00  
% 2.27/1.00  fof(f72,plain,(
% 2.27/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.00    inference(equality_resolution,[],[f48])).
% 2.27/1.00  
% 2.27/1.00  fof(f3,axiom,(
% 2.27/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k2_relat_1(X1) = k1_xboole_0 & k2_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f17,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.27/1.00    inference(ennf_transformation,[],[f3])).
% 2.27/1.00  
% 2.27/1.00  fof(f18,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (X0 = X1 | k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.27/1.00    inference(flattening,[],[f17])).
% 2.27/1.00  
% 2.27/1.00  fof(f44,plain,(
% 2.27/1.00    ( ! [X0,X1] : (X0 = X1 | k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f18])).
% 2.27/1.00  
% 2.27/1.00  fof(f10,axiom,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f29,plain,(
% 2.27/1.00    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.27/1.00    inference(ennf_transformation,[],[f10])).
% 2.27/1.00  
% 2.27/1.00  fof(f30,plain,(
% 2.27/1.00    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.27/1.00    inference(flattening,[],[f29])).
% 2.27/1.00  
% 2.27/1.00  fof(f58,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f30])).
% 2.27/1.00  
% 2.27/1.00  fof(f54,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f28])).
% 2.27/1.00  
% 2.27/1.00  fof(f56,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f28])).
% 2.27/1.00  
% 2.27/1.00  fof(f5,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f20,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/1.00    inference(ennf_transformation,[],[f5])).
% 2.27/1.00  
% 2.27/1.00  fof(f46,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f20])).
% 2.27/1.00  
% 2.27/1.00  fof(f2,axiom,(
% 2.27/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f43,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f2])).
% 2.27/1.00  
% 2.27/1.00  fof(f71,plain,(
% 2.27/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f70,plain,(
% 2.27/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f67,plain,(
% 2.27/1.00    v1_funct_2(sK2,sK0,sK0)),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f66,plain,(
% 2.27/1.00    v1_funct_1(sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f65,plain,(
% 2.27/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f64,plain,(
% 2.27/1.00    v3_funct_2(sK1,sK0,sK0)),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f63,plain,(
% 2.27/1.00    v1_funct_2(sK1,sK0,sK0)),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f62,plain,(
% 2.27/1.00    v1_funct_1(sK1)),
% 2.27/1.00    inference(cnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  cnf(c_12,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/1.00      | ~ v1_funct_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1052,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ v3_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 2.27/1.00      | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1535,plain,
% 2.27/1.00      ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 2.27/1.00      | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_7,plain,
% 2.27/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.27/1.00      | v2_funct_2(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.00      | ~ v1_funct_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_11,plain,
% 2.27/1.00      ( ~ v2_funct_2(X0,X1)
% 2.27/1.00      | ~ v5_relat_1(X0,X1)
% 2.27/1.00      | ~ v1_relat_1(X0)
% 2.27/1.00      | k2_relat_1(X0) = X1 ),
% 2.27/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_363,plain,
% 2.27/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.27/1.00      | ~ v5_relat_1(X3,X4)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.00      | ~ v1_funct_1(X0)
% 2.27/1.00      | ~ v1_relat_1(X3)
% 2.27/1.00      | X3 != X0
% 2.27/1.00      | X4 != X2
% 2.27/1.00      | k2_relat_1(X3) = X4 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_364,plain,
% 2.27/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.27/1.00      | ~ v5_relat_1(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.00      | ~ v1_funct_1(X0)
% 2.27/1.00      | ~ v1_relat_1(X0)
% 2.27/1.00      | k2_relat_1(X0) = X2 ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_363]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3,plain,
% 2.27/1.00      ( v5_relat_1(X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_380,plain,
% 2.27/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.00      | ~ v1_funct_1(X0)
% 2.27/1.00      | ~ v1_relat_1(X0)
% 2.27/1.00      | k2_relat_1(X0) = X2 ),
% 2.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_364,c_3]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1036,plain,
% 2.27/1.00      ( ~ v3_funct_2(X0_50,X0_49,X1_49)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | ~ v1_relat_1(X0_50)
% 2.27/1.00      | k2_relat_1(X0_50) = X1_49 ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_380]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1551,plain,
% 2.27/1.00      ( k2_relat_1(X0_50) = X0_49
% 2.27/1.00      | v3_funct_2(X0_50,X1_49,X0_49) != iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.27/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4922,plain,
% 2.27/1.00      ( k2_relat_1(k2_funct_2(X0_49,X0_50)) = X0_49
% 2.27/1.00      | v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49) != iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.27/1.00      | v1_funct_1(k2_funct_2(X0_49,X0_50)) != iProver_top
% 2.27/1.00      | v1_relat_1(k2_funct_2(X0_49,X0_50)) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1535,c_1551]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4924,plain,
% 2.27/1.00      ( k2_relat_1(k2_funct_2(sK0,sK1)) = sK0
% 2.27/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) != iProver_top
% 2.27/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.27/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
% 2.27/1.00      | v1_funct_1(sK1) != iProver_top
% 2.27/1.00      | v1_relat_1(k2_funct_2(sK0,sK1)) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4922]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1069,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
% 2.27/1.00      | r2_relset_1(X2_49,X3_49,X2_50,X3_50)
% 2.27/1.00      | X2_50 != X0_50
% 2.27/1.00      | X3_50 != X1_50
% 2.27/1.00      | X2_49 != X0_49
% 2.27/1.00      | X3_49 != X1_49 ),
% 2.27/1.00      theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2036,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
% 2.27/1.00      | r2_relset_1(X2_49,X3_49,sK2,X2_50)
% 2.27/1.00      | X2_50 != X1_50
% 2.27/1.00      | sK2 != X0_50
% 2.27/1.00      | X2_49 != X0_49
% 2.27/1.00      | X3_49 != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1069]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2341,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,sK2,X0_50)
% 2.27/1.00      | r2_relset_1(X2_49,X3_49,sK2,X1_50)
% 2.27/1.00      | X1_50 != X0_50
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | X2_49 != X0_49
% 2.27/1.00      | X3_49 != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2036]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2553,plain,
% 2.27/1.00      ( r2_relset_1(X0_49,X1_49,sK2,X0_50)
% 2.27/1.00      | ~ r2_relset_1(X2_49,X3_49,sK2,sK2)
% 2.27/1.00      | X0_50 != sK2
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | X0_49 != X2_49
% 2.27/1.00      | X1_49 != X3_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2341]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4165,plain,
% 2.27/1.00      ( r2_relset_1(X0_49,X1_49,sK2,k2_funct_1(sK1))
% 2.27/1.00      | ~ r2_relset_1(X2_49,X3_49,sK2,sK2)
% 2.27/1.00      | k2_funct_1(sK1) != sK2
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | X0_49 != X2_49
% 2.27/1.00      | X1_49 != X3_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2553]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4176,plain,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
% 2.27/1.00      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.27/1.00      | k2_funct_1(sK1) != sK2
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | sK0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4165]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_17,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | v2_funct_2(X3,X0)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3) ),
% 2.27/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_391,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ v5_relat_1(X4,X5)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_relat_1(X4)
% 2.27/1.00      | X3 != X4
% 2.27/1.00      | X0 != X5
% 2.27/1.00      | k2_relat_1(X4) = X5 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_392,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ v5_relat_1(X3,X0)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | ~ v1_relat_1(X3)
% 2.27/1.00      | k2_relat_1(X3) = X0 ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_416,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | ~ v1_relat_1(X3)
% 2.27/1.00      | k2_relat_1(X3) = X0 ),
% 2.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_392,c_3]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1035,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X0_49,k1_partfun1(X0_49,X1_49,X1_49,X0_49,X0_50,X1_50),k6_partfun1(X0_49))
% 2.27/1.00      | ~ v1_funct_2(X1_50,X1_49,X0_49)
% 2.27/1.00      | ~ v1_funct_2(X0_50,X0_49,X1_49)
% 2.27/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | ~ v1_funct_1(X1_50)
% 2.27/1.00      | ~ v1_relat_1(X1_50)
% 2.27/1.00      | k2_relat_1(X1_50) = X0_49 ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_416]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3484,plain,
% 2.27/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X0_49,X0_49,sK0,X0_50,sK2),k6_partfun1(sK0))
% 2.27/1.00      | ~ v1_funct_2(X0_50,sK0,X0_49)
% 2.27/1.00      | ~ v1_funct_2(sK2,X0_49,sK0)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 2.27/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | ~ v1_funct_1(sK2)
% 2.27/1.00      | ~ v1_relat_1(sK2)
% 2.27/1.00      | k2_relat_1(sK2) = sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1035]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3486,plain,
% 2.27/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
% 2.27/1.00      | ~ v1_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ v1_funct_2(sK2,sK0,sK0)
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_funct_1(sK1)
% 2.27/1.00      | ~ v1_funct_1(sK2)
% 2.27/1.00      | ~ v1_relat_1(sK2)
% 2.27/1.00      | k2_relat_1(sK2) = sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3484]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1063,plain,
% 2.27/1.00      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 2.27/1.00      theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1968,plain,
% 2.27/1.00      ( k2_relat_1(X0_50) != X0_49
% 2.27/1.00      | k2_relat_1(X0_50) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != X0_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3446,plain,
% 2.27/1.00      ( k2_relat_1(k2_funct_2(sK0,sK1)) != X0_49
% 2.27/1.00      | k2_relat_1(k2_funct_2(sK0,sK1)) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != X0_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3447,plain,
% 2.27/1.00      ( k2_relat_1(k2_funct_2(sK0,sK1)) != sK0
% 2.27/1.00      | k2_relat_1(k2_funct_2(sK0,sK1)) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3446]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3444,plain,
% 2.27/1.00      ( k2_relat_1(sK2) != X0_49
% 2.27/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != X0_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3445,plain,
% 2.27/1.00      ( k2_relat_1(sK2) != sK0
% 2.27/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3444]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_19,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ v2_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.27/1.00      | k2_funct_1(X2) = X3
% 2.27/1.00      | k1_xboole_0 = X1
% 2.27/1.00      | k1_xboole_0 = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_18,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | v2_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3) ),
% 2.27/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_167,plain,
% 2.27/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.27/1.00      | k2_funct_1(X2) = X3
% 2.27/1.00      | k1_xboole_0 = X1
% 2.27/1.00      | k1_xboole_0 = X0 ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_19,c_18]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_168,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.27/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | ~ v1_funct_1(X3)
% 2.27/1.00      | k2_relset_1(X0,X1,X2) != X1
% 2.27/1.00      | k2_funct_1(X2) = X3
% 2.27/1.00      | k1_xboole_0 = X0
% 2.27/1.00      | k1_xboole_0 = X1 ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_167]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1037,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X0_49,k1_partfun1(X0_49,X1_49,X1_49,X0_49,X0_50,X1_50),k6_partfun1(X0_49))
% 2.27/1.00      | ~ v1_funct_2(X1_50,X1_49,X0_49)
% 2.27/1.00      | ~ v1_funct_2(X0_50,X0_49,X1_49)
% 2.27/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | ~ v1_funct_1(X1_50)
% 2.27/1.00      | k2_funct_1(X0_50) = X1_50
% 2.27/1.00      | k2_relset_1(X0_49,X1_49,X0_50) != X1_49
% 2.27/1.00      | k1_xboole_0 = X0_49
% 2.27/1.00      | k1_xboole_0 = X1_49 ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_168]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3106,plain,
% 2.27/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
% 2.27/1.00      | ~ v1_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ v1_funct_2(sK2,sK0,sK0)
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_funct_1(sK1)
% 2.27/1.00      | ~ v1_funct_1(sK2)
% 2.27/1.00      | k2_funct_1(sK1) = sK2
% 2.27/1.00      | k2_relset_1(sK0,sK0,sK1) != sK0
% 2.27/1.00      | k1_xboole_0 = sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1037]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_0,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.00      | ~ v1_relat_1(X1)
% 2.27/1.00      | v1_relat_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1058,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.27/1.00      | ~ v1_relat_1(X1_50)
% 2.27/1.00      | v1_relat_1(X0_50) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1765,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | v1_relat_1(X0_50)
% 2.27/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1058]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2258,plain,
% 2.27/1.00      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | v1_relat_1(k2_funct_2(sK0,sK1))
% 2.27/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1765]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2259,plain,
% 2.27/1.00      ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.27/1.00      | v1_relat_1(k2_funct_2(sK0,sK1)) = iProver_top
% 2.27/1.00      | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2261,plain,
% 2.27/1.00      ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.27/1.00      | v1_relat_1(k2_funct_2(sK0,sK1)) = iProver_top
% 2.27/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2259]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2260,plain,
% 2.27/1.00      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | v1_relat_1(k2_funct_2(sK0,sK1))
% 2.27/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_22,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1045,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1542,plain,
% 2.27/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5,plain,
% 2.27/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1054,plain,
% 2.27/1.00      ( r2_relset_1(X0_49,X1_49,X0_50,X0_50)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1533,plain,
% 2.27/1.00      ( r2_relset_1(X0_49,X1_49,X0_50,X0_50) = iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2218,plain,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1542,c_1533]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2224,plain,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,sK2,sK2) ),
% 2.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2218]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2207,plain,
% 2.27/1.00      ( X0_49 != X1_49
% 2.27/1.00      | X0_49 = k2_relat_1(X0_50)
% 2.27/1.00      | k2_relat_1(X0_50) != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2208,plain,
% 2.27/1.00      ( k2_relat_1(sK1) != sK0 | sK0 = k2_relat_1(sK1) | sK0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2207]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2,plain,
% 2.27/1.00      ( ~ v1_relat_1(X0)
% 2.27/1.00      | ~ v1_relat_1(X1)
% 2.27/1.00      | X0 = X1
% 2.27/1.00      | k2_relat_1(X1) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1056,plain,
% 2.27/1.00      ( ~ v1_relat_1(X0_50)
% 2.27/1.00      | ~ v1_relat_1(X1_50)
% 2.27/1.00      | X0_50 = X1_50
% 2.27/1.00      | k2_relat_1(X0_50) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(X1_50) != k1_xboole_0 ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2023,plain,
% 2.27/1.00      ( ~ v1_relat_1(X0_50)
% 2.27/1.00      | ~ v1_relat_1(k2_funct_2(sK0,sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) = X0_50
% 2.27/1.00      | k2_relat_1(X0_50) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(k2_funct_2(sK0,sK1)) != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2025,plain,
% 2.27/1.00      ( ~ v1_relat_1(k2_funct_2(sK0,sK1))
% 2.27/1.00      | ~ v1_relat_1(sK1)
% 2.27/1.00      | k2_funct_2(sK0,sK1) = sK1
% 2.27/1.00      | k2_relat_1(k2_funct_2(sK0,sK1)) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(sK1) != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2023]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1798,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,X0_50,X1_50)
% 2.27/1.00      | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) != X1_50
% 2.27/1.00      | sK2 != X0_50
% 2.27/1.00      | sK0 != X0_49
% 2.27/1.00      | sK0 != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1069]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1929,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,sK2,X0_50)
% 2.27/1.00      | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) != X0_50
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | sK0 != X0_49
% 2.27/1.00      | sK0 != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2010,plain,
% 2.27/1.00      ( ~ r2_relset_1(X0_49,X1_49,sK2,k2_funct_1(sK1))
% 2.27/1.00      | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | sK0 != X0_49
% 2.27/1.00      | sK0 != X1_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1929]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2013,plain,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
% 2.27/1.00      | ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
% 2.27/1.00      | sK2 != sK2
% 2.27/1.00      | sK0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2010]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1969,plain,
% 2.27/1.00      ( k2_relat_1(sK1) != sK0
% 2.27/1.00      | k2_relat_1(sK1) = k1_xboole_0
% 2.27/1.00      | k1_xboole_0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1823,plain,
% 2.27/1.00      ( X0_49 != X1_49
% 2.27/1.00      | k2_relset_1(X2_49,X0_49,X0_50) != X1_49
% 2.27/1.00      | k2_relset_1(X2_49,X0_49,X0_50) = X0_49 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1921,plain,
% 2.27/1.00      ( X0_49 != k2_relat_1(X0_50)
% 2.27/1.00      | k2_relset_1(X1_49,X0_49,X0_50) = X0_49
% 2.27/1.00      | k2_relset_1(X1_49,X0_49,X0_50) != k2_relat_1(X0_50) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1823]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1922,plain,
% 2.27/1.00      ( k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1)
% 2.27/1.00      | k2_relset_1(sK0,sK0,sK1) = sK0
% 2.27/1.00      | sK0 != k2_relat_1(sK1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1921]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1529,plain,
% 2.27/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 2.27/1.00      | v1_relat_1(X1_50) != iProver_top
% 2.27/1.00      | v1_relat_1(X0_50) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1896,plain,
% 2.27/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.27/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1542,c_1529]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1906,plain,
% 2.27/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK2) ),
% 2.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1896]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1862,plain,
% 2.27/1.00      ( ~ v1_relat_1(X0_50)
% 2.27/1.00      | ~ v1_relat_1(sK2)
% 2.27/1.00      | sK2 = X0_50
% 2.27/1.00      | k2_relat_1(X0_50) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1864,plain,
% 2.27/1.00      ( ~ v1_relat_1(sK1)
% 2.27/1.00      | ~ v1_relat_1(sK2)
% 2.27/1.00      | sK2 = sK1
% 2.27/1.00      | k2_relat_1(sK1) != k1_xboole_0
% 2.27/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1862]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1061,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1839,plain,
% 2.27/1.00      ( sK2 = sK2 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1061]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1800,plain,
% 2.27/1.00      ( ~ r2_relset_1(sK0,sK0,sK1,sK1)
% 2.27/1.00      | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
% 2.27/1.00      | k2_funct_2(sK0,sK1) != sK1
% 2.27/1.00      | sK2 != sK1
% 2.27/1.00      | sK0 != sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1767,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.27/1.00      | v1_relat_1(sK1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1765]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1130,plain,
% 2.27/1.00      ( ~ v3_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_funct_1(sK1)
% 2.27/1.00      | ~ v1_relat_1(sK1)
% 2.27/1.00      | k2_relat_1(sK1) = sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1036]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_16,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/1.00      | ~ v1_funct_1(X0)
% 2.27/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1048,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ v3_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | k2_funct_2(X0_49,X0_50) = k2_funct_1(X0_50) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1114,plain,
% 2.27/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_funct_1(sK1)
% 2.27/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1048]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_15,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/1.00      | ~ v1_funct_1(X0)
% 2.27/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1049,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ v3_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50)
% 2.27/1.00      | v1_funct_1(k2_funct_2(X0_49,X0_50)) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1110,plain,
% 2.27/1.00      ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top
% 2.27/1.00      | v1_funct_1(k2_funct_2(X0_49,X0_50)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1112,plain,
% 2.27/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.27/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 2.27/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_13,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.27/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.27/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/1.00      | ~ v1_funct_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1051,plain,
% 2.27/1.00      ( ~ v1_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | ~ v3_funct_2(X0_50,X0_49,X0_49)
% 2.27/1.00      | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49)
% 2.27/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 2.27/1.00      | ~ v1_funct_1(X0_50) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1104,plain,
% 2.27/1.00      ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(k2_funct_2(X0_49,X0_50),X0_49,X0_49) = iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1106,plain,
% 2.27/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 2.27/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.27/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1104]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1101,plain,
% 2.27/1.00      ( v1_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | v3_funct_2(X0_50,X0_49,X0_49) != iProver_top
% 2.27/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 2.27/1.00      | m1_subset_1(k2_funct_2(X0_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 2.27/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1103,plain,
% 2.27/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 2.27/1.00      | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.27/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.27/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1101]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1102,plain,
% 2.27/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 2.27/1.00      | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | ~ v1_funct_1(sK1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1052]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1098,plain,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,sK1,sK1)
% 2.27/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1054]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1055,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.27/1.00      | k2_relset_1(X0_49,X1_49,X0_50) = k2_relat_1(X0_50) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1095,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.27/1.00      | k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1055]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1060,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1088,plain,
% 2.27/1.00      ( sK0 = sK0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1060]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1,plain,
% 2.27/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_92,plain,
% 2.27/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_94,plain,
% 2.27/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_93,plain,
% 2.27/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_20,negated_conjecture,
% 2.27/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_21,negated_conjecture,
% 2.27/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_24,negated_conjecture,
% 2.27/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_25,negated_conjecture,
% 2.27/1.00      ( v1_funct_1(sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_26,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_33,plain,
% 2.27/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_27,negated_conjecture,
% 2.27/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_32,plain,
% 2.27/1.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_28,negated_conjecture,
% 2.27/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_31,plain,
% 2.27/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_29,negated_conjecture,
% 2.27/1.00      ( v1_funct_1(sK1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_30,plain,
% 2.27/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(contradiction,plain,
% 2.27/1.00      ( $false ),
% 2.27/1.00      inference(minisat,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_4924,c_4176,c_3486,c_3447,c_3445,c_3106,c_2261,c_2260,
% 2.27/1.00                 c_2224,c_2208,c_2025,c_2013,c_1969,c_1922,c_1906,c_1864,
% 2.27/1.00                 c_1839,c_1800,c_1767,c_1130,c_1114,c_1112,c_1106,c_1103,
% 2.27/1.00                 c_1102,c_1098,c_1095,c_1088,c_94,c_93,c_20,c_21,c_22,
% 2.27/1.00                 c_24,c_25,c_33,c_26,c_32,c_27,c_31,c_28,c_30,c_29]) ).
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  ------                               Statistics
% 2.27/1.00  
% 2.27/1.00  ------ General
% 2.27/1.00  
% 2.27/1.00  abstr_ref_over_cycles:                  0
% 2.27/1.00  abstr_ref_under_cycles:                 0
% 2.27/1.00  gc_basic_clause_elim:                   0
% 2.27/1.00  forced_gc_time:                         0
% 2.27/1.00  parsing_time:                           0.011
% 2.27/1.00  unif_index_cands_time:                  0.
% 2.27/1.00  unif_index_add_time:                    0.
% 2.27/1.00  orderings_time:                         0.
% 2.27/1.00  out_proof_time:                         0.01
% 2.27/1.00  total_time:                             0.21
% 2.27/1.00  num_of_symbols:                         52
% 2.27/1.00  num_of_terms:                           5698
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing
% 2.27/1.00  
% 2.27/1.00  num_of_splits:                          0
% 2.27/1.00  num_of_split_atoms:                     0
% 2.27/1.00  num_of_reused_defs:                     0
% 2.27/1.00  num_eq_ax_congr_red:                    18
% 2.27/1.00  num_of_sem_filtered_clauses:            3
% 2.27/1.00  num_of_subtypes:                        3
% 2.27/1.00  monotx_restored_types:                  1
% 2.27/1.00  sat_num_of_epr_types:                   0
% 2.27/1.00  sat_num_of_non_cyclic_types:            0
% 2.27/1.00  sat_guarded_non_collapsed_types:        1
% 2.27/1.00  num_pure_diseq_elim:                    0
% 2.27/1.00  simp_replaced_by:                       0
% 2.27/1.00  res_preprocessed:                       134
% 2.27/1.00  prep_upred:                             0
% 2.27/1.00  prep_unflattend:                        46
% 2.27/1.00  smt_new_axioms:                         0
% 2.27/1.00  pred_elim_cands:                        6
% 2.27/1.00  pred_elim:                              2
% 2.27/1.00  pred_elim_cl:                           3
% 2.27/1.00  pred_elim_cycles:                       5
% 2.27/1.00  merged_defs:                            0
% 2.27/1.00  merged_defs_ncl:                        0
% 2.27/1.00  bin_hyper_res:                          0
% 2.27/1.00  prep_cycles:                            4
% 2.27/1.00  pred_elim_time:                         0.015
% 2.27/1.00  splitting_time:                         0.
% 2.27/1.00  sem_filter_time:                        0.
% 2.27/1.00  monotx_time:                            0.001
% 2.27/1.00  subtype_inf_time:                       0.001
% 2.27/1.00  
% 2.27/1.00  ------ Problem properties
% 2.27/1.00  
% 2.27/1.00  clauses:                                24
% 2.27/1.00  conjectures:                            10
% 2.27/1.00  epr:                                    6
% 2.27/1.00  horn:                                   23
% 2.27/1.00  ground:                                 10
% 2.27/1.00  unary:                                  11
% 2.27/1.00  binary:                                 2
% 2.27/1.00  lits:                                   77
% 2.27/1.00  lits_eq:                                12
% 2.27/1.00  fd_pure:                                0
% 2.27/1.00  fd_pseudo:                              0
% 2.27/1.00  fd_cond:                                0
% 2.27/1.00  fd_pseudo_cond:                         5
% 2.27/1.00  ac_symbols:                             0
% 2.27/1.00  
% 2.27/1.00  ------ Propositional Solver
% 2.27/1.00  
% 2.27/1.00  prop_solver_calls:                      28
% 2.27/1.00  prop_fast_solver_calls:                 1199
% 2.27/1.00  smt_solver_calls:                       0
% 2.27/1.00  smt_fast_solver_calls:                  0
% 2.27/1.00  prop_num_of_clauses:                    1481
% 2.27/1.00  prop_preprocess_simplified:             5101
% 2.27/1.00  prop_fo_subsumed:                       43
% 2.27/1.00  prop_solver_time:                       0.
% 2.27/1.00  smt_solver_time:                        0.
% 2.27/1.00  smt_fast_solver_time:                   0.
% 2.27/1.00  prop_fast_solver_time:                  0.
% 2.27/1.00  prop_unsat_core_time:                   0.
% 2.27/1.00  
% 2.27/1.00  ------ QBF
% 2.27/1.00  
% 2.27/1.00  qbf_q_res:                              0
% 2.27/1.00  qbf_num_tautologies:                    0
% 2.27/1.00  qbf_prep_cycles:                        0
% 2.27/1.00  
% 2.27/1.00  ------ BMC1
% 2.27/1.00  
% 2.27/1.00  bmc1_current_bound:                     -1
% 2.27/1.00  bmc1_last_solved_bound:                 -1
% 2.27/1.00  bmc1_unsat_core_size:                   -1
% 2.27/1.00  bmc1_unsat_core_parents_size:           -1
% 2.27/1.00  bmc1_merge_next_fun:                    0
% 2.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation
% 2.27/1.00  
% 2.27/1.00  inst_num_of_clauses:                    411
% 2.27/1.00  inst_num_in_passive:                    93
% 2.27/1.00  inst_num_in_active:                     258
% 2.27/1.00  inst_num_in_unprocessed:                60
% 2.27/1.00  inst_num_of_loops:                      310
% 2.27/1.00  inst_num_of_learning_restarts:          0
% 2.27/1.00  inst_num_moves_active_passive:          48
% 2.27/1.00  inst_lit_activity:                      0
% 2.27/1.00  inst_lit_activity_moves:                0
% 2.27/1.00  inst_num_tautologies:                   0
% 2.27/1.00  inst_num_prop_implied:                  0
% 2.27/1.00  inst_num_existing_simplified:           0
% 2.27/1.00  inst_num_eq_res_simplified:             0
% 2.27/1.00  inst_num_child_elim:                    0
% 2.27/1.00  inst_num_of_dismatching_blockings:      228
% 2.27/1.00  inst_num_of_non_proper_insts:           593
% 2.27/1.00  inst_num_of_duplicates:                 0
% 2.27/1.00  inst_inst_num_from_inst_to_res:         0
% 2.27/1.00  inst_dismatching_checking_time:         0.
% 2.27/1.00  
% 2.27/1.00  ------ Resolution
% 2.27/1.00  
% 2.27/1.00  res_num_of_clauses:                     0
% 2.27/1.00  res_num_in_passive:                     0
% 2.27/1.00  res_num_in_active:                      0
% 2.27/1.00  res_num_of_loops:                       138
% 2.27/1.00  res_forward_subset_subsumed:            61
% 2.27/1.00  res_backward_subset_subsumed:           0
% 2.27/1.00  res_forward_subsumed:                   0
% 2.27/1.00  res_backward_subsumed:                  0
% 2.27/1.00  res_forward_subsumption_resolution:     2
% 2.27/1.00  res_backward_subsumption_resolution:    0
% 2.27/1.00  res_clause_to_clause_subsumption:       199
% 2.27/1.00  res_orphan_elimination:                 0
% 2.27/1.00  res_tautology_del:                      82
% 2.27/1.00  res_num_eq_res_simplified:              0
% 2.27/1.00  res_num_sel_changes:                    0
% 2.27/1.00  res_moves_from_active_to_pass:          0
% 2.27/1.00  
% 2.27/1.00  ------ Superposition
% 2.27/1.00  
% 2.27/1.00  sup_time_total:                         0.
% 2.27/1.00  sup_time_generating:                    0.
% 2.27/1.00  sup_time_sim_full:                      0.
% 2.27/1.00  sup_time_sim_immed:                     0.
% 2.27/1.00  
% 2.27/1.00  sup_num_of_clauses:                     79
% 2.27/1.00  sup_num_in_active:                      23
% 2.27/1.00  sup_num_in_passive:                     56
% 2.27/1.00  sup_num_of_loops:                       60
% 2.27/1.00  sup_fw_superposition:                   30
% 2.27/1.00  sup_bw_superposition:                   32
% 2.27/1.00  sup_immediate_simplified:               4
% 2.27/1.00  sup_given_eliminated:                   0
% 2.27/1.00  comparisons_done:                       0
% 2.27/1.00  comparisons_avoided:                    0
% 2.27/1.00  
% 2.27/1.00  ------ Simplifications
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  sim_fw_subset_subsumed:                 0
% 2.27/1.00  sim_bw_subset_subsumed:                 0
% 2.27/1.00  sim_fw_subsumed:                        4
% 2.27/1.00  sim_bw_subsumed:                        0
% 2.27/1.00  sim_fw_subsumption_res:                 0
% 2.27/1.00  sim_bw_subsumption_res:                 0
% 2.27/1.00  sim_tautology_del:                      0
% 2.27/1.00  sim_eq_tautology_del:                   3
% 2.27/1.00  sim_eq_res_simp:                        0
% 2.27/1.00  sim_fw_demodulated:                     4
% 2.27/1.00  sim_bw_demodulated:                     38
% 2.27/1.00  sim_light_normalised:                   4
% 2.27/1.00  sim_joinable_taut:                      0
% 2.27/1.00  sim_joinable_simp:                      0
% 2.27/1.00  sim_ac_normalised:                      0
% 2.27/1.00  sim_smt_subsumption:                    0
% 2.27/1.00  
%------------------------------------------------------------------------------
