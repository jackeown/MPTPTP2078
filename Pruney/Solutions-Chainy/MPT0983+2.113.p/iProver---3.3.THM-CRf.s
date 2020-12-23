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
% DateTime   : Thu Dec  3 12:02:09 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 924 expanded)
%              Number of clauses        :  109 ( 276 expanded)
%              Number of leaves         :   25 ( 231 expanded)
%              Depth                    :   17
%              Number of atoms          :  625 (5781 expanded)
%              Number of equality atoms :  190 ( 440 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f23])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f55,f54])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f95,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f74,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f92,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_698,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7529,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_7531,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_7529])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1225,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1228,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1231,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4211,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1231])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4380,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4211,c_41])).

cnf(c_4381,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4380])).

cnf(c_4392,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_4381])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2402,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_3803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_4571,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4392,c_37,c_35,c_34,c_32,c_3803])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_397,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_56])).

cnf(c_1222,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_4574,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4571,c_1222])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4576,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_1234])).

cnf(c_4993,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_38,c_40,c_41,c_43,c_4576])).

cnf(c_4996,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_4993,c_4571])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1229,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5003,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4996,c_1229])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1237,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4997,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_1237])).

cnf(c_15,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4998,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4997,c_15])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2669,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1221])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1247,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2960,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_1247])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2870,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1240])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1239,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3020,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2870,c_1239])).

cnf(c_3825,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2960,c_3020])).

cnf(c_3826,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3825])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1242,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2888,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1241])).

cnf(c_3095,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_2888])).

cnf(c_3105,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3095])).

cnf(c_2871,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1240])).

cnf(c_3025,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2871,c_1239])).

cnf(c_3021,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3020])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1238,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2833,plain,
    ( v1_relat_1(k6_partfun1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1238])).

cnf(c_2834,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2833])).

cnf(c_2836,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2734,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2736,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_2604,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2606,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0)
    | sK0 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_689,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1615,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1617,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_1486,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1488,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK0)
    | sK0 != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_415,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_416,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_469,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_416])).

cnf(c_470,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_480,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_470,c_2])).

cnf(c_481,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_80,plain,
    ( v1_relat_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7531,c_5003,c_4998,c_3826,c_3105,c_3025,c_3021,c_3020,c_2836,c_2736,c_2606,c_1617,c_1488,c_481,c_480,c_0,c_84,c_83,c_80,c_43,c_42,c_41,c_40,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.73/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.02  
% 3.73/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.02  
% 3.73/1.02  ------  iProver source info
% 3.73/1.02  
% 3.73/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.02  git: non_committed_changes: false
% 3.73/1.02  git: last_make_outside_of_git: false
% 3.73/1.02  
% 3.73/1.02  ------ 
% 3.73/1.02  
% 3.73/1.02  ------ Input Options
% 3.73/1.02  
% 3.73/1.02  --out_options                           all
% 3.73/1.02  --tptp_safe_out                         true
% 3.73/1.02  --problem_path                          ""
% 3.73/1.02  --include_path                          ""
% 3.73/1.02  --clausifier                            res/vclausify_rel
% 3.73/1.02  --clausifier_options                    --mode clausify
% 3.73/1.02  --stdin                                 false
% 3.73/1.02  --stats_out                             all
% 3.73/1.02  
% 3.73/1.02  ------ General Options
% 3.73/1.02  
% 3.73/1.02  --fof                                   false
% 3.73/1.02  --time_out_real                         305.
% 3.73/1.02  --time_out_virtual                      -1.
% 3.73/1.02  --symbol_type_check                     false
% 3.73/1.02  --clausify_out                          false
% 3.73/1.02  --sig_cnt_out                           false
% 3.73/1.02  --trig_cnt_out                          false
% 3.73/1.02  --trig_cnt_out_tolerance                1.
% 3.73/1.02  --trig_cnt_out_sk_spl                   false
% 3.73/1.02  --abstr_cl_out                          false
% 3.73/1.02  
% 3.73/1.02  ------ Global Options
% 3.73/1.02  
% 3.73/1.02  --schedule                              default
% 3.73/1.02  --add_important_lit                     false
% 3.73/1.02  --prop_solver_per_cl                    1000
% 3.73/1.02  --min_unsat_core                        false
% 3.73/1.02  --soft_assumptions                      false
% 3.73/1.02  --soft_lemma_size                       3
% 3.73/1.02  --prop_impl_unit_size                   0
% 3.73/1.02  --prop_impl_unit                        []
% 3.73/1.02  --share_sel_clauses                     true
% 3.73/1.02  --reset_solvers                         false
% 3.73/1.02  --bc_imp_inh                            [conj_cone]
% 3.73/1.02  --conj_cone_tolerance                   3.
% 3.73/1.02  --extra_neg_conj                        none
% 3.73/1.02  --large_theory_mode                     true
% 3.73/1.02  --prolific_symb_bound                   200
% 3.73/1.02  --lt_threshold                          2000
% 3.73/1.02  --clause_weak_htbl                      true
% 3.73/1.02  --gc_record_bc_elim                     false
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing Options
% 3.73/1.02  
% 3.73/1.02  --preprocessing_flag                    true
% 3.73/1.02  --time_out_prep_mult                    0.1
% 3.73/1.02  --splitting_mode                        input
% 3.73/1.02  --splitting_grd                         true
% 3.73/1.02  --splitting_cvd                         false
% 3.73/1.02  --splitting_cvd_svl                     false
% 3.73/1.02  --splitting_nvd                         32
% 3.73/1.02  --sub_typing                            true
% 3.73/1.02  --prep_gs_sim                           true
% 3.73/1.02  --prep_unflatten                        true
% 3.73/1.02  --prep_res_sim                          true
% 3.73/1.02  --prep_upred                            true
% 3.73/1.02  --prep_sem_filter                       exhaustive
% 3.73/1.02  --prep_sem_filter_out                   false
% 3.73/1.02  --pred_elim                             true
% 3.73/1.02  --res_sim_input                         true
% 3.73/1.02  --eq_ax_congr_red                       true
% 3.73/1.02  --pure_diseq_elim                       true
% 3.73/1.02  --brand_transform                       false
% 3.73/1.02  --non_eq_to_eq                          false
% 3.73/1.02  --prep_def_merge                        true
% 3.73/1.02  --prep_def_merge_prop_impl              false
% 3.73/1.02  --prep_def_merge_mbd                    true
% 3.73/1.02  --prep_def_merge_tr_red                 false
% 3.73/1.02  --prep_def_merge_tr_cl                  false
% 3.73/1.02  --smt_preprocessing                     true
% 3.73/1.02  --smt_ac_axioms                         fast
% 3.73/1.02  --preprocessed_out                      false
% 3.73/1.02  --preprocessed_stats                    false
% 3.73/1.02  
% 3.73/1.02  ------ Abstraction refinement Options
% 3.73/1.02  
% 3.73/1.02  --abstr_ref                             []
% 3.73/1.02  --abstr_ref_prep                        false
% 3.73/1.02  --abstr_ref_until_sat                   false
% 3.73/1.02  --abstr_ref_sig_restrict                funpre
% 3.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.02  --abstr_ref_under                       []
% 3.73/1.02  
% 3.73/1.02  ------ SAT Options
% 3.73/1.02  
% 3.73/1.02  --sat_mode                              false
% 3.73/1.02  --sat_fm_restart_options                ""
% 3.73/1.02  --sat_gr_def                            false
% 3.73/1.02  --sat_epr_types                         true
% 3.73/1.02  --sat_non_cyclic_types                  false
% 3.73/1.02  --sat_finite_models                     false
% 3.73/1.02  --sat_fm_lemmas                         false
% 3.73/1.02  --sat_fm_prep                           false
% 3.73/1.02  --sat_fm_uc_incr                        true
% 3.73/1.02  --sat_out_model                         small
% 3.73/1.02  --sat_out_clauses                       false
% 3.73/1.02  
% 3.73/1.02  ------ QBF Options
% 3.73/1.02  
% 3.73/1.02  --qbf_mode                              false
% 3.73/1.02  --qbf_elim_univ                         false
% 3.73/1.02  --qbf_dom_inst                          none
% 3.73/1.02  --qbf_dom_pre_inst                      false
% 3.73/1.02  --qbf_sk_in                             false
% 3.73/1.02  --qbf_pred_elim                         true
% 3.73/1.02  --qbf_split                             512
% 3.73/1.02  
% 3.73/1.02  ------ BMC1 Options
% 3.73/1.02  
% 3.73/1.02  --bmc1_incremental                      false
% 3.73/1.02  --bmc1_axioms                           reachable_all
% 3.73/1.02  --bmc1_min_bound                        0
% 3.73/1.02  --bmc1_max_bound                        -1
% 3.73/1.02  --bmc1_max_bound_default                -1
% 3.73/1.02  --bmc1_symbol_reachability              true
% 3.73/1.02  --bmc1_property_lemmas                  false
% 3.73/1.02  --bmc1_k_induction                      false
% 3.73/1.02  --bmc1_non_equiv_states                 false
% 3.73/1.02  --bmc1_deadlock                         false
% 3.73/1.02  --bmc1_ucm                              false
% 3.73/1.02  --bmc1_add_unsat_core                   none
% 3.73/1.02  --bmc1_unsat_core_children              false
% 3.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.02  --bmc1_out_stat                         full
% 3.73/1.02  --bmc1_ground_init                      false
% 3.73/1.02  --bmc1_pre_inst_next_state              false
% 3.73/1.02  --bmc1_pre_inst_state                   false
% 3.73/1.02  --bmc1_pre_inst_reach_state             false
% 3.73/1.02  --bmc1_out_unsat_core                   false
% 3.73/1.02  --bmc1_aig_witness_out                  false
% 3.73/1.02  --bmc1_verbose                          false
% 3.73/1.02  --bmc1_dump_clauses_tptp                false
% 3.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.02  --bmc1_dump_file                        -
% 3.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.02  --bmc1_ucm_extend_mode                  1
% 3.73/1.02  --bmc1_ucm_init_mode                    2
% 3.73/1.02  --bmc1_ucm_cone_mode                    none
% 3.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.02  --bmc1_ucm_relax_model                  4
% 3.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.02  --bmc1_ucm_layered_model                none
% 3.73/1.02  --bmc1_ucm_max_lemma_size               10
% 3.73/1.02  
% 3.73/1.02  ------ AIG Options
% 3.73/1.02  
% 3.73/1.02  --aig_mode                              false
% 3.73/1.02  
% 3.73/1.02  ------ Instantiation Options
% 3.73/1.02  
% 3.73/1.02  --instantiation_flag                    true
% 3.73/1.02  --inst_sos_flag                         false
% 3.73/1.02  --inst_sos_phase                        true
% 3.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.02  --inst_lit_sel_side                     num_symb
% 3.73/1.02  --inst_solver_per_active                1400
% 3.73/1.02  --inst_solver_calls_frac                1.
% 3.73/1.02  --inst_passive_queue_type               priority_queues
% 3.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.02  --inst_passive_queues_freq              [25;2]
% 3.73/1.02  --inst_dismatching                      true
% 3.73/1.02  --inst_eager_unprocessed_to_passive     true
% 3.73/1.02  --inst_prop_sim_given                   true
% 3.73/1.02  --inst_prop_sim_new                     false
% 3.73/1.02  --inst_subs_new                         false
% 3.73/1.02  --inst_eq_res_simp                      false
% 3.73/1.02  --inst_subs_given                       false
% 3.73/1.02  --inst_orphan_elimination               true
% 3.73/1.02  --inst_learning_loop_flag               true
% 3.73/1.02  --inst_learning_start                   3000
% 3.73/1.02  --inst_learning_factor                  2
% 3.73/1.02  --inst_start_prop_sim_after_learn       3
% 3.73/1.02  --inst_sel_renew                        solver
% 3.73/1.02  --inst_lit_activity_flag                true
% 3.73/1.02  --inst_restr_to_given                   false
% 3.73/1.02  --inst_activity_threshold               500
% 3.73/1.02  --inst_out_proof                        true
% 3.73/1.02  
% 3.73/1.02  ------ Resolution Options
% 3.73/1.02  
% 3.73/1.02  --resolution_flag                       true
% 3.73/1.02  --res_lit_sel                           adaptive
% 3.73/1.02  --res_lit_sel_side                      none
% 3.73/1.02  --res_ordering                          kbo
% 3.73/1.02  --res_to_prop_solver                    active
% 3.73/1.02  --res_prop_simpl_new                    false
% 3.73/1.02  --res_prop_simpl_given                  true
% 3.73/1.02  --res_passive_queue_type                priority_queues
% 3.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.02  --res_passive_queues_freq               [15;5]
% 3.73/1.02  --res_forward_subs                      full
% 3.73/1.02  --res_backward_subs                     full
% 3.73/1.02  --res_forward_subs_resolution           true
% 3.73/1.02  --res_backward_subs_resolution          true
% 3.73/1.02  --res_orphan_elimination                true
% 3.73/1.02  --res_time_limit                        2.
% 3.73/1.02  --res_out_proof                         true
% 3.73/1.02  
% 3.73/1.02  ------ Superposition Options
% 3.73/1.02  
% 3.73/1.02  --superposition_flag                    true
% 3.73/1.02  --sup_passive_queue_type                priority_queues
% 3.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.02  --demod_completeness_check              fast
% 3.73/1.02  --demod_use_ground                      true
% 3.73/1.02  --sup_to_prop_solver                    passive
% 3.73/1.02  --sup_prop_simpl_new                    true
% 3.73/1.02  --sup_prop_simpl_given                  true
% 3.73/1.02  --sup_fun_splitting                     false
% 3.73/1.02  --sup_smt_interval                      50000
% 3.73/1.02  
% 3.73/1.02  ------ Superposition Simplification Setup
% 3.73/1.02  
% 3.73/1.02  --sup_indices_passive                   []
% 3.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_full_bw                           [BwDemod]
% 3.73/1.02  --sup_immed_triv                        [TrivRules]
% 3.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_immed_bw_main                     []
% 3.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.02  
% 3.73/1.02  ------ Combination Options
% 3.73/1.02  
% 3.73/1.02  --comb_res_mult                         3
% 3.73/1.02  --comb_sup_mult                         2
% 3.73/1.02  --comb_inst_mult                        10
% 3.73/1.02  
% 3.73/1.02  ------ Debug Options
% 3.73/1.02  
% 3.73/1.02  --dbg_backtrace                         false
% 3.73/1.02  --dbg_dump_prop_clauses                 false
% 3.73/1.02  --dbg_dump_prop_clauses_file            -
% 3.73/1.02  --dbg_out_stat                          false
% 3.73/1.02  ------ Parsing...
% 3.73/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.02  ------ Proving...
% 3.73/1.02  ------ Problem Properties 
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  clauses                                 31
% 3.73/1.02  conjectures                             6
% 3.73/1.02  EPR                                     9
% 3.73/1.02  Horn                                    30
% 3.73/1.02  unary                                   15
% 3.73/1.02  binary                                  3
% 3.73/1.02  lits                                    77
% 3.73/1.02  lits eq                                 8
% 3.73/1.02  fd_pure                                 0
% 3.73/1.02  fd_pseudo                               0
% 3.73/1.02  fd_cond                                 1
% 3.73/1.02  fd_pseudo_cond                          2
% 3.73/1.02  AC symbols                              0
% 3.73/1.02  
% 3.73/1.02  ------ Schedule dynamic 5 is on 
% 3.73/1.02  
% 3.73/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  ------ 
% 3.73/1.02  Current options:
% 3.73/1.02  ------ 
% 3.73/1.02  
% 3.73/1.02  ------ Input Options
% 3.73/1.02  
% 3.73/1.02  --out_options                           all
% 3.73/1.02  --tptp_safe_out                         true
% 3.73/1.02  --problem_path                          ""
% 3.73/1.02  --include_path                          ""
% 3.73/1.02  --clausifier                            res/vclausify_rel
% 3.73/1.02  --clausifier_options                    --mode clausify
% 3.73/1.02  --stdin                                 false
% 3.73/1.02  --stats_out                             all
% 3.73/1.02  
% 3.73/1.02  ------ General Options
% 3.73/1.02  
% 3.73/1.02  --fof                                   false
% 3.73/1.02  --time_out_real                         305.
% 3.73/1.02  --time_out_virtual                      -1.
% 3.73/1.02  --symbol_type_check                     false
% 3.73/1.02  --clausify_out                          false
% 3.73/1.02  --sig_cnt_out                           false
% 3.73/1.02  --trig_cnt_out                          false
% 3.73/1.02  --trig_cnt_out_tolerance                1.
% 3.73/1.02  --trig_cnt_out_sk_spl                   false
% 3.73/1.02  --abstr_cl_out                          false
% 3.73/1.02  
% 3.73/1.02  ------ Global Options
% 3.73/1.02  
% 3.73/1.02  --schedule                              default
% 3.73/1.02  --add_important_lit                     false
% 3.73/1.02  --prop_solver_per_cl                    1000
% 3.73/1.02  --min_unsat_core                        false
% 3.73/1.02  --soft_assumptions                      false
% 3.73/1.02  --soft_lemma_size                       3
% 3.73/1.02  --prop_impl_unit_size                   0
% 3.73/1.02  --prop_impl_unit                        []
% 3.73/1.02  --share_sel_clauses                     true
% 3.73/1.02  --reset_solvers                         false
% 3.73/1.02  --bc_imp_inh                            [conj_cone]
% 3.73/1.02  --conj_cone_tolerance                   3.
% 3.73/1.02  --extra_neg_conj                        none
% 3.73/1.02  --large_theory_mode                     true
% 3.73/1.02  --prolific_symb_bound                   200
% 3.73/1.02  --lt_threshold                          2000
% 3.73/1.02  --clause_weak_htbl                      true
% 3.73/1.02  --gc_record_bc_elim                     false
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing Options
% 3.73/1.02  
% 3.73/1.02  --preprocessing_flag                    true
% 3.73/1.02  --time_out_prep_mult                    0.1
% 3.73/1.02  --splitting_mode                        input
% 3.73/1.02  --splitting_grd                         true
% 3.73/1.02  --splitting_cvd                         false
% 3.73/1.02  --splitting_cvd_svl                     false
% 3.73/1.02  --splitting_nvd                         32
% 3.73/1.02  --sub_typing                            true
% 3.73/1.02  --prep_gs_sim                           true
% 3.73/1.02  --prep_unflatten                        true
% 3.73/1.02  --prep_res_sim                          true
% 3.73/1.02  --prep_upred                            true
% 3.73/1.02  --prep_sem_filter                       exhaustive
% 3.73/1.02  --prep_sem_filter_out                   false
% 3.73/1.02  --pred_elim                             true
% 3.73/1.02  --res_sim_input                         true
% 3.73/1.02  --eq_ax_congr_red                       true
% 3.73/1.02  --pure_diseq_elim                       true
% 3.73/1.02  --brand_transform                       false
% 3.73/1.02  --non_eq_to_eq                          false
% 3.73/1.02  --prep_def_merge                        true
% 3.73/1.02  --prep_def_merge_prop_impl              false
% 3.73/1.02  --prep_def_merge_mbd                    true
% 3.73/1.02  --prep_def_merge_tr_red                 false
% 3.73/1.02  --prep_def_merge_tr_cl                  false
% 3.73/1.02  --smt_preprocessing                     true
% 3.73/1.02  --smt_ac_axioms                         fast
% 3.73/1.02  --preprocessed_out                      false
% 3.73/1.02  --preprocessed_stats                    false
% 3.73/1.02  
% 3.73/1.02  ------ Abstraction refinement Options
% 3.73/1.02  
% 3.73/1.02  --abstr_ref                             []
% 3.73/1.02  --abstr_ref_prep                        false
% 3.73/1.02  --abstr_ref_until_sat                   false
% 3.73/1.02  --abstr_ref_sig_restrict                funpre
% 3.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.02  --abstr_ref_under                       []
% 3.73/1.02  
% 3.73/1.02  ------ SAT Options
% 3.73/1.02  
% 3.73/1.02  --sat_mode                              false
% 3.73/1.02  --sat_fm_restart_options                ""
% 3.73/1.02  --sat_gr_def                            false
% 3.73/1.02  --sat_epr_types                         true
% 3.73/1.02  --sat_non_cyclic_types                  false
% 3.73/1.02  --sat_finite_models                     false
% 3.73/1.02  --sat_fm_lemmas                         false
% 3.73/1.02  --sat_fm_prep                           false
% 3.73/1.02  --sat_fm_uc_incr                        true
% 3.73/1.02  --sat_out_model                         small
% 3.73/1.02  --sat_out_clauses                       false
% 3.73/1.02  
% 3.73/1.02  ------ QBF Options
% 3.73/1.02  
% 3.73/1.02  --qbf_mode                              false
% 3.73/1.02  --qbf_elim_univ                         false
% 3.73/1.02  --qbf_dom_inst                          none
% 3.73/1.02  --qbf_dom_pre_inst                      false
% 3.73/1.02  --qbf_sk_in                             false
% 3.73/1.02  --qbf_pred_elim                         true
% 3.73/1.02  --qbf_split                             512
% 3.73/1.02  
% 3.73/1.02  ------ BMC1 Options
% 3.73/1.02  
% 3.73/1.02  --bmc1_incremental                      false
% 3.73/1.02  --bmc1_axioms                           reachable_all
% 3.73/1.02  --bmc1_min_bound                        0
% 3.73/1.02  --bmc1_max_bound                        -1
% 3.73/1.02  --bmc1_max_bound_default                -1
% 3.73/1.02  --bmc1_symbol_reachability              true
% 3.73/1.02  --bmc1_property_lemmas                  false
% 3.73/1.02  --bmc1_k_induction                      false
% 3.73/1.02  --bmc1_non_equiv_states                 false
% 3.73/1.02  --bmc1_deadlock                         false
% 3.73/1.02  --bmc1_ucm                              false
% 3.73/1.02  --bmc1_add_unsat_core                   none
% 3.73/1.02  --bmc1_unsat_core_children              false
% 3.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.02  --bmc1_out_stat                         full
% 3.73/1.02  --bmc1_ground_init                      false
% 3.73/1.02  --bmc1_pre_inst_next_state              false
% 3.73/1.02  --bmc1_pre_inst_state                   false
% 3.73/1.02  --bmc1_pre_inst_reach_state             false
% 3.73/1.02  --bmc1_out_unsat_core                   false
% 3.73/1.02  --bmc1_aig_witness_out                  false
% 3.73/1.02  --bmc1_verbose                          false
% 3.73/1.02  --bmc1_dump_clauses_tptp                false
% 3.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.02  --bmc1_dump_file                        -
% 3.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.02  --bmc1_ucm_extend_mode                  1
% 3.73/1.02  --bmc1_ucm_init_mode                    2
% 3.73/1.02  --bmc1_ucm_cone_mode                    none
% 3.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.02  --bmc1_ucm_relax_model                  4
% 3.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.02  --bmc1_ucm_layered_model                none
% 3.73/1.02  --bmc1_ucm_max_lemma_size               10
% 3.73/1.02  
% 3.73/1.02  ------ AIG Options
% 3.73/1.02  
% 3.73/1.02  --aig_mode                              false
% 3.73/1.02  
% 3.73/1.02  ------ Instantiation Options
% 3.73/1.02  
% 3.73/1.02  --instantiation_flag                    true
% 3.73/1.02  --inst_sos_flag                         false
% 3.73/1.02  --inst_sos_phase                        true
% 3.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.02  --inst_lit_sel_side                     none
% 3.73/1.02  --inst_solver_per_active                1400
% 3.73/1.02  --inst_solver_calls_frac                1.
% 3.73/1.02  --inst_passive_queue_type               priority_queues
% 3.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.02  --inst_passive_queues_freq              [25;2]
% 3.73/1.02  --inst_dismatching                      true
% 3.73/1.02  --inst_eager_unprocessed_to_passive     true
% 3.73/1.02  --inst_prop_sim_given                   true
% 3.73/1.02  --inst_prop_sim_new                     false
% 3.73/1.02  --inst_subs_new                         false
% 3.73/1.02  --inst_eq_res_simp                      false
% 3.73/1.02  --inst_subs_given                       false
% 3.73/1.02  --inst_orphan_elimination               true
% 3.73/1.02  --inst_learning_loop_flag               true
% 3.73/1.02  --inst_learning_start                   3000
% 3.73/1.02  --inst_learning_factor                  2
% 3.73/1.02  --inst_start_prop_sim_after_learn       3
% 3.73/1.02  --inst_sel_renew                        solver
% 3.73/1.02  --inst_lit_activity_flag                true
% 3.73/1.02  --inst_restr_to_given                   false
% 3.73/1.02  --inst_activity_threshold               500
% 3.73/1.02  --inst_out_proof                        true
% 3.73/1.02  
% 3.73/1.02  ------ Resolution Options
% 3.73/1.02  
% 3.73/1.02  --resolution_flag                       false
% 3.73/1.02  --res_lit_sel                           adaptive
% 3.73/1.02  --res_lit_sel_side                      none
% 3.73/1.02  --res_ordering                          kbo
% 3.73/1.02  --res_to_prop_solver                    active
% 3.73/1.02  --res_prop_simpl_new                    false
% 3.73/1.02  --res_prop_simpl_given                  true
% 3.73/1.02  --res_passive_queue_type                priority_queues
% 3.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.02  --res_passive_queues_freq               [15;5]
% 3.73/1.02  --res_forward_subs                      full
% 3.73/1.02  --res_backward_subs                     full
% 3.73/1.02  --res_forward_subs_resolution           true
% 3.73/1.02  --res_backward_subs_resolution          true
% 3.73/1.02  --res_orphan_elimination                true
% 3.73/1.02  --res_time_limit                        2.
% 3.73/1.02  --res_out_proof                         true
% 3.73/1.02  
% 3.73/1.02  ------ Superposition Options
% 3.73/1.02  
% 3.73/1.02  --superposition_flag                    true
% 3.73/1.02  --sup_passive_queue_type                priority_queues
% 3.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.02  --demod_completeness_check              fast
% 3.73/1.02  --demod_use_ground                      true
% 3.73/1.02  --sup_to_prop_solver                    passive
% 3.73/1.02  --sup_prop_simpl_new                    true
% 3.73/1.02  --sup_prop_simpl_given                  true
% 3.73/1.02  --sup_fun_splitting                     false
% 3.73/1.02  --sup_smt_interval                      50000
% 3.73/1.02  
% 3.73/1.02  ------ Superposition Simplification Setup
% 3.73/1.02  
% 3.73/1.02  --sup_indices_passive                   []
% 3.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_full_bw                           [BwDemod]
% 3.73/1.02  --sup_immed_triv                        [TrivRules]
% 3.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_immed_bw_main                     []
% 3.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.02  
% 3.73/1.02  ------ Combination Options
% 3.73/1.02  
% 3.73/1.02  --comb_res_mult                         3
% 3.73/1.02  --comb_sup_mult                         2
% 3.73/1.02  --comb_inst_mult                        10
% 3.73/1.02  
% 3.73/1.02  ------ Debug Options
% 3.73/1.02  
% 3.73/1.02  --dbg_backtrace                         false
% 3.73/1.02  --dbg_dump_prop_clauses                 false
% 3.73/1.02  --dbg_dump_prop_clauses_file            -
% 3.73/1.02  --dbg_out_stat                          false
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  ------ Proving...
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  % SZS status Theorem for theBenchmark.p
% 3.73/1.02  
% 3.73/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.02  
% 3.73/1.02  fof(f23,conjecture,(
% 3.73/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f24,negated_conjecture,(
% 3.73/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.73/1.02    inference(negated_conjecture,[],[f23])).
% 3.73/1.02  
% 3.73/1.02  fof(f47,plain,(
% 3.73/1.02    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.73/1.02    inference(ennf_transformation,[],[f24])).
% 3.73/1.02  
% 3.73/1.02  fof(f48,plain,(
% 3.73/1.02    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.73/1.02    inference(flattening,[],[f47])).
% 3.73/1.02  
% 3.73/1.02  fof(f55,plain,(
% 3.73/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.73/1.02    introduced(choice_axiom,[])).
% 3.73/1.02  
% 3.73/1.02  fof(f54,plain,(
% 3.73/1.02    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.73/1.02    introduced(choice_axiom,[])).
% 3.73/1.02  
% 3.73/1.02  fof(f56,plain,(
% 3.73/1.02    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f55,f54])).
% 3.73/1.02  
% 3.73/1.02  fof(f90,plain,(
% 3.73/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f93,plain,(
% 3.73/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f20,axiom,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f43,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.73/1.02    inference(ennf_transformation,[],[f20])).
% 3.73/1.02  
% 3.73/1.02  fof(f44,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.73/1.02    inference(flattening,[],[f43])).
% 3.73/1.02  
% 3.73/1.02  fof(f84,plain,(
% 3.73/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f44])).
% 3.73/1.02  
% 3.73/1.02  fof(f91,plain,(
% 3.73/1.02    v1_funct_1(sK3)),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f88,plain,(
% 3.73/1.02    v1_funct_1(sK2)),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f16,axiom,(
% 3.73/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f37,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.73/1.02    inference(ennf_transformation,[],[f16])).
% 3.73/1.02  
% 3.73/1.02  fof(f38,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.02    inference(flattening,[],[f37])).
% 3.73/1.02  
% 3.73/1.02  fof(f52,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.02    inference(nnf_transformation,[],[f38])).
% 3.73/1.02  
% 3.73/1.02  fof(f77,plain,(
% 3.73/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f52])).
% 3.73/1.02  
% 3.73/1.02  fof(f94,plain,(
% 3.73/1.02    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f19,axiom,(
% 3.73/1.02    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f25,plain,(
% 3.73/1.02    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.73/1.02    inference(pure_predicate_removal,[],[f19])).
% 3.73/1.02  
% 3.73/1.02  fof(f83,plain,(
% 3.73/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f25])).
% 3.73/1.02  
% 3.73/1.02  fof(f18,axiom,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f41,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.73/1.02    inference(ennf_transformation,[],[f18])).
% 3.73/1.02  
% 3.73/1.02  fof(f42,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.73/1.02    inference(flattening,[],[f41])).
% 3.73/1.02  
% 3.73/1.02  fof(f82,plain,(
% 3.73/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f42])).
% 3.73/1.02  
% 3.73/1.02  fof(f22,axiom,(
% 3.73/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f45,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.73/1.02    inference(ennf_transformation,[],[f22])).
% 3.73/1.02  
% 3.73/1.02  fof(f46,plain,(
% 3.73/1.02    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.73/1.02    inference(flattening,[],[f45])).
% 3.73/1.02  
% 3.73/1.02  fof(f86,plain,(
% 3.73/1.02    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f46])).
% 3.73/1.02  
% 3.73/1.02  fof(f12,axiom,(
% 3.73/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f35,plain,(
% 3.73/1.02    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/1.02    inference(ennf_transformation,[],[f12])).
% 3.73/1.02  
% 3.73/1.02  fof(f71,plain,(
% 3.73/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f35])).
% 3.73/1.02  
% 3.73/1.02  fof(f13,axiom,(
% 3.73/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f73,plain,(
% 3.73/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.73/1.02    inference(cnf_transformation,[],[f13])).
% 3.73/1.02  
% 3.73/1.02  fof(f21,axiom,(
% 3.73/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f85,plain,(
% 3.73/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f21])).
% 3.73/1.02  
% 3.73/1.02  fof(f96,plain,(
% 3.73/1.02    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.73/1.02    inference(definition_unfolding,[],[f73,f85])).
% 3.73/1.02  
% 3.73/1.02  fof(f15,axiom,(
% 3.73/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f26,plain,(
% 3.73/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.73/1.02    inference(pure_predicate_removal,[],[f15])).
% 3.73/1.02  
% 3.73/1.02  fof(f36,plain,(
% 3.73/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.02    inference(ennf_transformation,[],[f26])).
% 3.73/1.02  
% 3.73/1.02  fof(f76,plain,(
% 3.73/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f36])).
% 3.73/1.02  
% 3.73/1.02  fof(f9,axiom,(
% 3.73/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f32,plain,(
% 3.73/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/1.02    inference(ennf_transformation,[],[f9])).
% 3.73/1.02  
% 3.73/1.02  fof(f51,plain,(
% 3.73/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.73/1.02    inference(nnf_transformation,[],[f32])).
% 3.73/1.02  
% 3.73/1.02  fof(f67,plain,(
% 3.73/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f51])).
% 3.73/1.02  
% 3.73/1.02  fof(f2,axiom,(
% 3.73/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f49,plain,(
% 3.73/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.02    inference(nnf_transformation,[],[f2])).
% 3.73/1.02  
% 3.73/1.02  fof(f50,plain,(
% 3.73/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.02    inference(flattening,[],[f49])).
% 3.73/1.02  
% 3.73/1.02  fof(f60,plain,(
% 3.73/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f50])).
% 3.73/1.02  
% 3.73/1.02  fof(f8,axiom,(
% 3.73/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f31,plain,(
% 3.73/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.73/1.02    inference(ennf_transformation,[],[f8])).
% 3.73/1.02  
% 3.73/1.02  fof(f66,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f31])).
% 3.73/1.02  
% 3.73/1.02  fof(f10,axiom,(
% 3.73/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f69,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f10])).
% 3.73/1.02  
% 3.73/1.02  fof(f6,axiom,(
% 3.73/1.02    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f29,plain,(
% 3.73/1.02    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.73/1.02    inference(ennf_transformation,[],[f6])).
% 3.73/1.02  
% 3.73/1.02  fof(f64,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f29])).
% 3.73/1.02  
% 3.73/1.02  fof(f7,axiom,(
% 3.73/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f30,plain,(
% 3.73/1.02    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.73/1.02    inference(ennf_transformation,[],[f7])).
% 3.73/1.02  
% 3.73/1.02  fof(f65,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f30])).
% 3.73/1.02  
% 3.73/1.02  fof(f11,axiom,(
% 3.73/1.02    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f33,plain,(
% 3.73/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.73/1.02    inference(ennf_transformation,[],[f11])).
% 3.73/1.02  
% 3.73/1.02  fof(f34,plain,(
% 3.73/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.73/1.02    inference(flattening,[],[f33])).
% 3.73/1.02  
% 3.73/1.02  fof(f70,plain,(
% 3.73/1.02    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f34])).
% 3.73/1.02  
% 3.73/1.02  fof(f4,axiom,(
% 3.73/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f27,plain,(
% 3.73/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.73/1.02    inference(ennf_transformation,[],[f4])).
% 3.73/1.02  
% 3.73/1.02  fof(f62,plain,(
% 3.73/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f27])).
% 3.73/1.02  
% 3.73/1.02  fof(f68,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f51])).
% 3.73/1.02  
% 3.73/1.02  fof(f17,axiom,(
% 3.73/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f39,plain,(
% 3.73/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.73/1.02    inference(ennf_transformation,[],[f17])).
% 3.73/1.02  
% 3.73/1.02  fof(f40,plain,(
% 3.73/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.73/1.02    inference(flattening,[],[f39])).
% 3.73/1.02  
% 3.73/1.02  fof(f53,plain,(
% 3.73/1.02    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.73/1.02    inference(nnf_transformation,[],[f40])).
% 3.73/1.02  
% 3.73/1.02  fof(f80,plain,(
% 3.73/1.02    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/1.02    inference(cnf_transformation,[],[f53])).
% 3.73/1.02  
% 3.73/1.02  fof(f103,plain,(
% 3.73/1.02    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.73/1.02    inference(equality_resolution,[],[f80])).
% 3.73/1.02  
% 3.73/1.02  fof(f95,plain,(
% 3.73/1.02    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f59,plain,(
% 3.73/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.73/1.02    inference(cnf_transformation,[],[f50])).
% 3.73/1.02  
% 3.73/1.02  fof(f100,plain,(
% 3.73/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.02    inference(equality_resolution,[],[f59])).
% 3.73/1.02  
% 3.73/1.02  fof(f1,axiom,(
% 3.73/1.02    v1_xboole_0(k1_xboole_0)),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f57,plain,(
% 3.73/1.02    v1_xboole_0(k1_xboole_0)),
% 3.73/1.02    inference(cnf_transformation,[],[f1])).
% 3.73/1.02  
% 3.73/1.02  fof(f14,axiom,(
% 3.73/1.02    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.02  
% 3.73/1.02  fof(f75,plain,(
% 3.73/1.02    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f14])).
% 3.73/1.02  
% 3.73/1.02  fof(f98,plain,(
% 3.73/1.02    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.73/1.02    inference(definition_unfolding,[],[f75,f85])).
% 3.73/1.02  
% 3.73/1.02  fof(f74,plain,(
% 3.73/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.73/1.02    inference(cnf_transformation,[],[f14])).
% 3.73/1.02  
% 3.73/1.02  fof(f99,plain,(
% 3.73/1.02    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.73/1.02    inference(definition_unfolding,[],[f74,f85])).
% 3.73/1.02  
% 3.73/1.02  fof(f92,plain,(
% 3.73/1.02    v1_funct_2(sK3,sK1,sK0)),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  fof(f89,plain,(
% 3.73/1.02    v1_funct_2(sK2,sK0,sK1)),
% 3.73/1.02    inference(cnf_transformation,[],[f56])).
% 3.73/1.02  
% 3.73/1.02  cnf(c_698,plain,
% 3.73/1.02      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.73/1.02      theory(equality) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_7529,plain,
% 3.73/1.02      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_698]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_7531,plain,
% 3.73/1.02      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_7529]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_35,negated_conjecture,
% 3.73/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.73/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1225,plain,
% 3.73/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_32,negated_conjecture,
% 3.73/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.73/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1228,plain,
% 3.73/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_27,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.73/1.02      | ~ v1_funct_1(X0)
% 3.73/1.02      | ~ v1_funct_1(X3)
% 3.73/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1231,plain,
% 3.73/1.02      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.73/1.02      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.73/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/1.02      | v1_funct_1(X5) != iProver_top
% 3.73/1.02      | v1_funct_1(X4) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4211,plain,
% 3.73/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.73/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/1.02      | v1_funct_1(X2) != iProver_top
% 3.73/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1228,c_1231]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_34,negated_conjecture,
% 3.73/1.02      ( v1_funct_1(sK3) ),
% 3.73/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_41,plain,
% 3.73/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4380,plain,
% 3.73/1.02      ( v1_funct_1(X2) != iProver_top
% 3.73/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/1.02      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.73/1.02      inference(global_propositional_subsumption,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_4211,c_41]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4381,plain,
% 3.73/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.73/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/1.02      | v1_funct_1(X2) != iProver_top ),
% 3.73/1.02      inference(renaming,[status(thm)],[c_4380]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4392,plain,
% 3.73/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.73/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1225,c_4381]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_37,negated_conjecture,
% 3.73/1.02      ( v1_funct_1(sK2) ),
% 3.73/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1585,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.73/1.02      | ~ v1_funct_1(X0)
% 3.73/1.02      | ~ v1_funct_1(sK3)
% 3.73/1.02      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_27]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1850,plain,
% 3.73/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.73/1.02      | ~ v1_funct_1(sK2)
% 3.73/1.02      | ~ v1_funct_1(sK3)
% 3.73/1.02      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_1585]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2402,plain,
% 3.73/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.02      | ~ v1_funct_1(sK2)
% 3.73/1.02      | ~ v1_funct_1(sK3)
% 3.73/1.02      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_1850]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3803,plain,
% 3.73/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/1.02      | ~ v1_funct_1(sK2)
% 3.73/1.02      | ~ v1_funct_1(sK3)
% 3.73/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_2402]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4571,plain,
% 3.73/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.73/1.02      inference(global_propositional_subsumption,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_4392,c_37,c_35,c_34,c_32,c_3803]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_21,plain,
% 3.73/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.73/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.02      | X3 = X2 ),
% 3.73/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_31,negated_conjecture,
% 3.73/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_396,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | X3 = X0
% 3.73/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.73/1.02      | k6_partfun1(sK0) != X3
% 3.73/1.02      | sK0 != X2
% 3.73/1.02      | sK0 != X1 ),
% 3.73/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_397,plain,
% 3.73/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.73/1.02      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.73/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.73/1.02      inference(unflattening,[status(thm)],[c_396]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_26,plain,
% 3.73/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.73/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_56,plain,
% 3.73/1.02      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_26]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_399,plain,
% 3.73/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.73/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.73/1.02      inference(global_propositional_subsumption,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_397,c_56]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1222,plain,
% 3.73/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.73/1.02      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4574,plain,
% 3.73/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.73/1.02      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.73/1.02      inference(demodulation,[status(thm)],[c_4571,c_1222]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_38,plain,
% 3.73/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_40,plain,
% 3.73/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_43,plain,
% 3.73/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_24,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.73/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.73/1.02      | ~ v1_funct_1(X0)
% 3.73/1.02      | ~ v1_funct_1(X3) ),
% 3.73/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1234,plain,
% 3.73/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.73/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.73/1.02      | v1_funct_1(X0) != iProver_top
% 3.73/1.02      | v1_funct_1(X3) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4576,plain,
% 3.73/1.02      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.73/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.73/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/1.02      | v1_funct_1(sK2) != iProver_top
% 3.73/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_4571,c_1234]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4993,plain,
% 3.73/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.73/1.02      inference(global_propositional_subsumption,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_4574,c_38,c_40,c_41,c_43,c_4576]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4996,plain,
% 3.73/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.73/1.02      inference(demodulation,[status(thm)],[c_4993,c_4571]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_29,plain,
% 3.73/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/1.02      | ~ v1_funct_2(X3,X4,X1)
% 3.73/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.73/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | ~ v1_funct_1(X0)
% 3.73/1.02      | ~ v1_funct_1(X3)
% 3.73/1.02      | v2_funct_1(X3)
% 3.73/1.02      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.73/1.02      | k1_xboole_0 = X2 ),
% 3.73/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1229,plain,
% 3.73/1.02      ( k1_xboole_0 = X0
% 3.73/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.73/1.02      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.73/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.73/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.73/1.02      | v1_funct_1(X1) != iProver_top
% 3.73/1.02      | v1_funct_1(X3) != iProver_top
% 3.73/1.02      | v2_funct_1(X3) = iProver_top
% 3.73/1.02      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_5003,plain,
% 3.73/1.02      ( sK0 = k1_xboole_0
% 3.73/1.02      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.73/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.73/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.73/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/1.02      | v1_funct_1(sK2) != iProver_top
% 3.73/1.02      | v1_funct_1(sK3) != iProver_top
% 3.73/1.02      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.73/1.02      | v2_funct_1(sK2) = iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_4996,c_1229]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_14,plain,
% 3.73/1.02      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.73/1.02      | ~ v1_relat_1(X0)
% 3.73/1.02      | ~ v1_relat_1(X1) ),
% 3.73/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1237,plain,
% 3.73/1.02      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.73/1.02      | v1_relat_1(X0) != iProver_top
% 3.73/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4997,plain,
% 3.73/1.02      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.73/1.02      | v1_relat_1(sK2) != iProver_top
% 3.73/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_4993,c_1237]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_15,plain,
% 3.73/1.02      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.73/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_4998,plain,
% 3.73/1.02      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.73/1.02      | v1_relat_1(sK2) != iProver_top
% 3.73/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.02      inference(demodulation,[status(thm)],[c_4997,c_15]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_19,plain,
% 3.73/1.02      ( v5_relat_1(X0,X1)
% 3.73/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.73/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_11,plain,
% 3.73/1.02      ( ~ v5_relat_1(X0,X1)
% 3.73/1.02      | r1_tarski(k2_relat_1(X0),X1)
% 3.73/1.02      | ~ v1_relat_1(X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_436,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 3.73/1.02      | ~ v1_relat_1(X0) ),
% 3.73/1.02      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1221,plain,
% 3.73/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/1.02      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.73/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2669,plain,
% 3.73/1.02      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.73/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1228,c_1221]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1,plain,
% 3.73/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.73/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1247,plain,
% 3.73/1.02      ( X0 = X1
% 3.73/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.73/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2960,plain,
% 3.73/1.02      ( k2_relat_1(sK3) = sK0
% 3.73/1.02      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.73/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_2669,c_1247]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_9,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/1.02      | ~ v1_relat_1(X1)
% 3.73/1.02      | v1_relat_1(X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1240,plain,
% 3.73/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/1.02      | v1_relat_1(X1) != iProver_top
% 3.73/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2870,plain,
% 3.73/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.73/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1228,c_1240]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_12,plain,
% 3.73/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1239,plain,
% 3.73/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3020,plain,
% 3.73/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.73/1.02      inference(forward_subsumption_resolution,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_2870,c_1239]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3825,plain,
% 3.73/1.02      ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.73/1.02      | k2_relat_1(sK3) = sK0 ),
% 3.73/1.02      inference(global_propositional_subsumption,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_2960,c_3020]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3826,plain,
% 3.73/1.02      ( k2_relat_1(sK3) = sK0
% 3.73/1.02      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 3.73/1.02      inference(renaming,[status(thm)],[c_3825]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_7,plain,
% 3.73/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1242,plain,
% 3.73/1.02      ( v1_xboole_0(X0) != iProver_top
% 3.73/1.02      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_8,plain,
% 3.73/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/1.02      | ~ v1_xboole_0(X1)
% 3.73/1.02      | v1_xboole_0(X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1241,plain,
% 3.73/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/1.02      | v1_xboole_0(X1) != iProver_top
% 3.73/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2888,plain,
% 3.73/1.02      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.73/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1225,c_1241]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3095,plain,
% 3.73/1.02      ( v1_xboole_0(sK2) = iProver_top
% 3.73/1.02      | v1_xboole_0(sK0) != iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1242,c_2888]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3105,plain,
% 3.73/1.02      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 3.73/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_3095]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2871,plain,
% 3.73/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.73/1.02      | v1_relat_1(sK2) = iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_1225,c_1240]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3025,plain,
% 3.73/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 3.73/1.02      inference(forward_subsumption_resolution,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_2871,c_1239]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_3021,plain,
% 3.73/1.02      ( v1_relat_1(sK3) ),
% 3.73/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_3020]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_13,plain,
% 3.73/1.02      ( ~ v1_relat_1(X0)
% 3.73/1.02      | v1_xboole_0(X0)
% 3.73/1.02      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1238,plain,
% 3.73/1.02      ( v1_relat_1(X0) != iProver_top
% 3.73/1.02      | v1_xboole_0(X0) = iProver_top
% 3.73/1.02      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2833,plain,
% 3.73/1.02      ( v1_relat_1(k6_partfun1(X0)) != iProver_top
% 3.73/1.02      | v1_xboole_0(X0) != iProver_top
% 3.73/1.02      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 3.73/1.02      inference(superposition,[status(thm)],[c_15,c_1238]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2834,plain,
% 3.73/1.02      ( ~ v1_relat_1(k6_partfun1(X0))
% 3.73/1.02      | ~ v1_xboole_0(X0)
% 3.73/1.02      | v1_xboole_0(k6_partfun1(X0)) ),
% 3.73/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2833]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2836,plain,
% 3.73/1.02      ( ~ v1_relat_1(k6_partfun1(sK0))
% 3.73/1.02      | v1_xboole_0(k6_partfun1(sK0))
% 3.73/1.02      | ~ v1_xboole_0(sK0) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_2834]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_5,plain,
% 3.73/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.73/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2734,plain,
% 3.73/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2736,plain,
% 3.73/1.02      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_2734]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2604,plain,
% 3.73/1.02      ( ~ v1_xboole_0(X0)
% 3.73/1.02      | ~ v1_xboole_0(k6_partfun1(X1))
% 3.73/1.02      | X0 = k6_partfun1(X1) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2606,plain,
% 3.73/1.02      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 3.73/1.02      | ~ v1_xboole_0(sK0)
% 3.73/1.02      | sK0 = k6_partfun1(sK0) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_2604]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_689,plain,
% 3.73/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.73/1.02      theory(equality) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1615,plain,
% 3.73/1.02      ( v1_xboole_0(X0)
% 3.73/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.73/1.02      | X0 != k1_xboole_0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_689]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1617,plain,
% 3.73/1.02      ( v1_xboole_0(sK0)
% 3.73/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.73/1.02      | sK0 != k1_xboole_0 ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_1615]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1486,plain,
% 3.73/1.02      ( v2_funct_1(X0)
% 3.73/1.02      | ~ v2_funct_1(k6_partfun1(X1))
% 3.73/1.02      | X0 != k6_partfun1(X1) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_698]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_1488,plain,
% 3.73/1.02      ( ~ v2_funct_1(k6_partfun1(sK0))
% 3.73/1.02      | v2_funct_1(sK0)
% 3.73/1.02      | sK0 != k6_partfun1(sK0) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_1486]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_10,plain,
% 3.73/1.02      ( v5_relat_1(X0,X1)
% 3.73/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.73/1.02      | ~ v1_relat_1(X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_22,plain,
% 3.73/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.73/1.02      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.73/1.02      | ~ v1_relat_1(X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_30,negated_conjecture,
% 3.73/1.02      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.73/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_415,plain,
% 3.73/1.02      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.73/1.02      | ~ v2_funct_1(sK2)
% 3.73/1.02      | ~ v1_relat_1(X0)
% 3.73/1.02      | k2_relat_1(X0) != sK0
% 3.73/1.02      | sK3 != X0 ),
% 3.73/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_416,plain,
% 3.73/1.02      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.73/1.02      | ~ v2_funct_1(sK2)
% 3.73/1.02      | ~ v1_relat_1(sK3)
% 3.73/1.02      | k2_relat_1(sK3) != sK0 ),
% 3.73/1.02      inference(unflattening,[status(thm)],[c_415]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_469,plain,
% 3.73/1.02      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.73/1.02      | ~ v2_funct_1(sK2)
% 3.73/1.02      | ~ v1_relat_1(X0)
% 3.73/1.02      | ~ v1_relat_1(sK3)
% 3.73/1.02      | k2_relat_1(sK3) != X1
% 3.73/1.02      | k2_relat_1(sK3) != sK0
% 3.73/1.02      | sK3 != X0 ),
% 3.73/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_416]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_470,plain,
% 3.73/1.02      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.73/1.02      | ~ v2_funct_1(sK2)
% 3.73/1.02      | ~ v1_relat_1(sK3)
% 3.73/1.02      | k2_relat_1(sK3) != sK0 ),
% 3.73/1.02      inference(unflattening,[status(thm)],[c_469]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_2,plain,
% 3.73/1.02      ( r1_tarski(X0,X0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_480,plain,
% 3.73/1.02      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.73/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_470,c_2]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_481,plain,
% 3.73/1.02      ( k2_relat_1(sK3) != sK0
% 3.73/1.02      | v2_funct_1(sK2) != iProver_top
% 3.73/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_0,plain,
% 3.73/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_17,plain,
% 3.73/1.02      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_82,plain,
% 3.73/1.02      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_84,plain,
% 3.73/1.02      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_82]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_83,plain,
% 3.73/1.02      ( v2_funct_1(k6_partfun1(sK0)) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_18,plain,
% 3.73/1.02      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.73/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_80,plain,
% 3.73/1.02      ( v1_relat_1(k6_partfun1(sK0)) ),
% 3.73/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_33,negated_conjecture,
% 3.73/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.73/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_42,plain,
% 3.73/1.02      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_36,negated_conjecture,
% 3.73/1.02      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.73/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(c_39,plain,
% 3.73/1.02      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.73/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.73/1.02  
% 3.73/1.02  cnf(contradiction,plain,
% 3.73/1.02      ( $false ),
% 3.73/1.02      inference(minisat,
% 3.73/1.02                [status(thm)],
% 3.73/1.02                [c_7531,c_5003,c_4998,c_3826,c_3105,c_3025,c_3021,c_3020,
% 3.73/1.02                 c_2836,c_2736,c_2606,c_1617,c_1488,c_481,c_480,c_0,c_84,
% 3.73/1.02                 c_83,c_80,c_43,c_42,c_41,c_40,c_39,c_38]) ).
% 3.73/1.02  
% 3.73/1.02  
% 3.73/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.02  
% 3.73/1.02  ------                               Statistics
% 3.73/1.02  
% 3.73/1.02  ------ General
% 3.73/1.02  
% 3.73/1.02  abstr_ref_over_cycles:                  0
% 3.73/1.02  abstr_ref_under_cycles:                 0
% 3.73/1.02  gc_basic_clause_elim:                   0
% 3.73/1.02  forced_gc_time:                         0
% 3.73/1.02  parsing_time:                           0.012
% 3.73/1.02  unif_index_cands_time:                  0.
% 3.73/1.02  unif_index_add_time:                    0.
% 3.73/1.02  orderings_time:                         0.
% 3.73/1.02  out_proof_time:                         0.02
% 3.73/1.02  total_time:                             0.377
% 3.73/1.02  num_of_symbols:                         53
% 3.73/1.02  num_of_terms:                           10211
% 3.73/1.02  
% 3.73/1.02  ------ Preprocessing
% 3.73/1.02  
% 3.73/1.02  num_of_splits:                          0
% 3.73/1.02  num_of_split_atoms:                     0
% 3.73/1.02  num_of_reused_defs:                     0
% 3.73/1.02  num_eq_ax_congr_red:                    7
% 3.73/1.02  num_of_sem_filtered_clauses:            1
% 3.73/1.02  num_of_subtypes:                        0
% 3.73/1.02  monotx_restored_types:                  0
% 3.73/1.02  sat_num_of_epr_types:                   0
% 3.73/1.02  sat_num_of_non_cyclic_types:            0
% 3.73/1.02  sat_guarded_non_collapsed_types:        0
% 3.73/1.02  num_pure_diseq_elim:                    0
% 3.73/1.02  simp_replaced_by:                       0
% 3.73/1.02  res_preprocessed:                       161
% 3.73/1.02  prep_upred:                             0
% 3.73/1.02  prep_unflattend:                        15
% 3.73/1.02  smt_new_axioms:                         0
% 3.73/1.02  pred_elim_cands:                        7
% 3.73/1.02  pred_elim:                              3
% 3.73/1.02  pred_elim_cl:                           6
% 3.73/1.02  pred_elim_cycles:                       5
% 3.73/1.02  merged_defs:                            0
% 3.73/1.02  merged_defs_ncl:                        0
% 3.73/1.02  bin_hyper_res:                          0
% 3.73/1.02  prep_cycles:                            4
% 3.73/1.02  pred_elim_time:                         0.003
% 3.73/1.02  splitting_time:                         0.
% 3.73/1.02  sem_filter_time:                        0.
% 3.73/1.02  monotx_time:                            0.
% 3.73/1.02  subtype_inf_time:                       0.
% 3.73/1.02  
% 3.73/1.02  ------ Problem properties
% 3.73/1.02  
% 3.73/1.02  clauses:                                31
% 3.73/1.02  conjectures:                            6
% 3.73/1.02  epr:                                    9
% 3.73/1.02  horn:                                   30
% 3.73/1.02  ground:                                 9
% 3.73/1.02  unary:                                  15
% 3.73/1.02  binary:                                 3
% 3.73/1.02  lits:                                   77
% 3.73/1.02  lits_eq:                                8
% 3.73/1.02  fd_pure:                                0
% 3.73/1.02  fd_pseudo:                              0
% 3.73/1.02  fd_cond:                                1
% 3.73/1.02  fd_pseudo_cond:                         2
% 3.73/1.02  ac_symbols:                             0
% 3.73/1.02  
% 3.73/1.02  ------ Propositional Solver
% 3.73/1.02  
% 3.73/1.02  prop_solver_calls:                      27
% 3.73/1.02  prop_fast_solver_calls:                 1070
% 3.73/1.02  smt_solver_calls:                       0
% 3.73/1.02  smt_fast_solver_calls:                  0
% 3.73/1.02  prop_num_of_clauses:                    3469
% 3.73/1.02  prop_preprocess_simplified:             9886
% 3.73/1.02  prop_fo_subsumed:                       21
% 3.73/1.02  prop_solver_time:                       0.
% 3.73/1.02  smt_solver_time:                        0.
% 3.73/1.02  smt_fast_solver_time:                   0.
% 3.73/1.02  prop_fast_solver_time:                  0.
% 3.73/1.02  prop_unsat_core_time:                   0.
% 3.73/1.02  
% 3.73/1.02  ------ QBF
% 3.73/1.02  
% 3.73/1.02  qbf_q_res:                              0
% 3.73/1.02  qbf_num_tautologies:                    0
% 3.73/1.02  qbf_prep_cycles:                        0
% 3.73/1.02  
% 3.73/1.02  ------ BMC1
% 3.73/1.02  
% 3.73/1.02  bmc1_current_bound:                     -1
% 3.73/1.02  bmc1_last_solved_bound:                 -1
% 3.73/1.02  bmc1_unsat_core_size:                   -1
% 3.73/1.02  bmc1_unsat_core_parents_size:           -1
% 3.73/1.02  bmc1_merge_next_fun:                    0
% 3.73/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.02  
% 3.73/1.02  ------ Instantiation
% 3.73/1.02  
% 3.73/1.02  inst_num_of_clauses:                    909
% 3.73/1.02  inst_num_in_passive:                    493
% 3.73/1.02  inst_num_in_active:                     350
% 3.73/1.02  inst_num_in_unprocessed:                65
% 3.73/1.02  inst_num_of_loops:                      405
% 3.73/1.02  inst_num_of_learning_restarts:          0
% 3.73/1.02  inst_num_moves_active_passive:          53
% 3.73/1.02  inst_lit_activity:                      0
% 3.73/1.02  inst_lit_activity_moves:                0
% 3.73/1.02  inst_num_tautologies:                   0
% 3.73/1.02  inst_num_prop_implied:                  0
% 3.73/1.02  inst_num_existing_simplified:           0
% 3.73/1.02  inst_num_eq_res_simplified:             0
% 3.73/1.02  inst_num_child_elim:                    0
% 3.73/1.02  inst_num_of_dismatching_blockings:      20
% 3.73/1.02  inst_num_of_non_proper_insts:           516
% 3.73/1.02  inst_num_of_duplicates:                 0
% 3.73/1.02  inst_inst_num_from_inst_to_res:         0
% 3.73/1.02  inst_dismatching_checking_time:         0.
% 3.73/1.02  
% 3.73/1.02  ------ Resolution
% 3.73/1.02  
% 3.73/1.02  res_num_of_clauses:                     0
% 3.73/1.02  res_num_in_passive:                     0
% 3.73/1.02  res_num_in_active:                      0
% 3.73/1.02  res_num_of_loops:                       165
% 3.73/1.02  res_forward_subset_subsumed:            28
% 3.73/1.02  res_backward_subset_subsumed:           0
% 3.73/1.02  res_forward_subsumed:                   0
% 3.73/1.02  res_backward_subsumed:                  1
% 3.73/1.02  res_forward_subsumption_resolution:     1
% 3.73/1.02  res_backward_subsumption_resolution:    0
% 3.73/1.02  res_clause_to_clause_subsumption:       311
% 3.73/1.02  res_orphan_elimination:                 0
% 3.73/1.02  res_tautology_del:                      17
% 3.73/1.03  res_num_eq_res_simplified:              0
% 3.73/1.03  res_num_sel_changes:                    0
% 3.73/1.03  res_moves_from_active_to_pass:          0
% 3.73/1.03  
% 3.73/1.03  ------ Superposition
% 3.73/1.03  
% 3.73/1.03  sup_time_total:                         0.
% 3.73/1.03  sup_time_generating:                    0.
% 3.73/1.03  sup_time_sim_full:                      0.
% 3.73/1.03  sup_time_sim_immed:                     0.
% 3.73/1.03  
% 3.73/1.03  sup_num_of_clauses:                     134
% 3.73/1.03  sup_num_in_active:                      74
% 3.73/1.03  sup_num_in_passive:                     60
% 3.73/1.03  sup_num_of_loops:                       80
% 3.73/1.03  sup_fw_superposition:                   59
% 3.73/1.03  sup_bw_superposition:                   71
% 3.73/1.03  sup_immediate_simplified:               16
% 3.73/1.03  sup_given_eliminated:                   1
% 3.73/1.03  comparisons_done:                       0
% 3.73/1.03  comparisons_avoided:                    0
% 3.73/1.03  
% 3.73/1.03  ------ Simplifications
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  sim_fw_subset_subsumed:                 6
% 3.73/1.03  sim_bw_subset_subsumed:                 2
% 3.73/1.03  sim_fw_subsumed:                        4
% 3.73/1.03  sim_bw_subsumed:                        0
% 3.73/1.03  sim_fw_subsumption_res:                 3
% 3.73/1.03  sim_bw_subsumption_res:                 0
% 3.73/1.03  sim_tautology_del:                      4
% 3.73/1.03  sim_eq_tautology_del:                   3
% 3.73/1.03  sim_eq_res_simp:                        0
% 3.73/1.03  sim_fw_demodulated:                     4
% 3.73/1.03  sim_bw_demodulated:                     5
% 3.73/1.03  sim_light_normalised:                   5
% 3.73/1.03  sim_joinable_taut:                      0
% 3.73/1.03  sim_joinable_simp:                      0
% 3.73/1.03  sim_ac_normalised:                      0
% 3.73/1.03  sim_smt_subsumption:                    0
% 3.73/1.03  
%------------------------------------------------------------------------------
