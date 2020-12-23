%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:19 EST 2020

% Result     : Timeout 59.11s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  208 (2246 expanded)
%              Number of clauses        :  120 ( 753 expanded)
%              Number of leaves         :   23 ( 537 expanded)
%              Depth                    :   24
%              Number of atoms          :  749 (16864 expanded)
%              Number of equality atoms :  347 (6021 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,conjecture,(
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

fof(f36,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f35])).

fof(f81,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f82,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f81])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f82,f88,f87])).

fof(f144,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f77])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f146,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

fof(f139,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

fof(f140,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f89])).

fof(f141,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

fof(f142,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

fof(f143,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f134,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f111,f134])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f145,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f89])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f75])).

fof(f133,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f73])).

fof(f131,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f71])).

fof(f86,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f30,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f132,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f152,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f102,f134])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f65])).

fof(f123,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f122,f134])).

fof(f150,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1899,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1907,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4712,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1899,c_1907])).

cnf(c_44,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_52,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_686,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_52])).

cnf(c_687,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_788,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_687])).

cnf(c_1891,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2597,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1891])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_60,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_61,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_63,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_64,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_2871,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2597,c_60,c_61,c_62,c_63,c_64,c_65])).

cnf(c_4718,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4712,c_2871])).

cnf(c_29,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1914,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11658,plain,
    ( k1_relat_1(X0) != sK0
    | v2_funct_1(k5_relat_1(sK3,X0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4718,c_1914])).

cnf(c_20,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_143,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_145,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3258,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3259,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3258])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3695,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3696,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3695])).

cnf(c_36,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1908,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4695,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1899,c_1908])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1933,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1896,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_4713,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1896,c_1907])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_4715,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4713,c_53])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1918,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12015,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_1918])).

cnf(c_3261,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3262,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3261])).

cnf(c_3698,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3699,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3698])).

cnf(c_12479,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12015,c_60,c_62,c_3262,c_3699])).

cnf(c_12488,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | v4_relat_1(X0,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_12479])).

cnf(c_14945,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4695,c_12488])).

cnf(c_4696,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1908])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1927,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6233,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4696,c_1927])).

cnf(c_7088,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6233,c_62,c_3262,c_3699])).

cnf(c_1935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7260,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1935])).

cnf(c_7658,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7260,c_62,c_3262,c_3699])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1930,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7663,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_7658,c_1930])).

cnf(c_8501,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7088,c_7663])).

cnf(c_8518,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8501,c_4715])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1903,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_12129,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1899,c_1903])).

cnf(c_12501,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12129,c_63])).

cnf(c_12502,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12501])).

cnf(c_12514,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_12502])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_52])).

cnf(c_673,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_42,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_82,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_675,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_82])).

cnf(c_1892,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_7980,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1892])).

cnf(c_11539,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7980,c_60,c_62,c_63,c_65])).

cnf(c_12532,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12514,c_11539])).

cnf(c_13436,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12532,c_60])).

cnf(c_7259,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1899,c_1935])).

cnf(c_7518,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7259,c_65,c_3259,c_3696])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1928,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8393,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7658,c_1928])).

cnf(c_9074,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_7518,c_8393])).

cnf(c_13439,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_13436,c_9074])).

cnf(c_13,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f152])).

cnf(c_13440,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_13439,c_13])).

cnf(c_14958,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14945,c_8518,c_13440])).

cnf(c_14966,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14958,c_65,c_3259,c_3696])).

cnf(c_28,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1915,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12288,plain,
    ( k1_relat_1(X0) != sK1
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_1915])).

cnf(c_13020,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK1
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12288,c_60,c_62,c_3262,c_3699])).

cnf(c_13021,plain,
    ( k1_relat_1(X0) != sK1
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13020])).

cnf(c_14985,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14966,c_13021])).

cnf(c_15014,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14985,c_13436])).

cnf(c_123731,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11658,c_63,c_65,c_145,c_3259,c_3696,c_15014])).

cnf(c_33,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1910,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_123750,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_123731,c_1910])).

cnf(c_32,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_1911,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13441,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13436,c_1911])).

cnf(c_13442,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13441,c_4715,c_4718])).

cnf(c_13443,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13442])).

cnf(c_17503,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13443,c_60,c_62,c_63,c_65,c_145,c_3259,c_3262,c_3696,c_3699,c_14958,c_15014])).

cnf(c_123754,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_123750,c_17503])).

cnf(c_48,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f150])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_123754,c_3696,c_3259,c_48,c_65,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 59.11/8.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.11/8.00  
% 59.11/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.11/8.00  
% 59.11/8.00  ------  iProver source info
% 59.11/8.00  
% 59.11/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.11/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.11/8.00  git: non_committed_changes: false
% 59.11/8.00  git: last_make_outside_of_git: false
% 59.11/8.00  
% 59.11/8.00  ------ 
% 59.11/8.00  
% 59.11/8.00  ------ Input Options
% 59.11/8.00  
% 59.11/8.00  --out_options                           all
% 59.11/8.00  --tptp_safe_out                         true
% 59.11/8.00  --problem_path                          ""
% 59.11/8.00  --include_path                          ""
% 59.11/8.00  --clausifier                            res/vclausify_rel
% 59.11/8.00  --clausifier_options                    --mode clausify
% 59.11/8.00  --stdin                                 false
% 59.11/8.00  --stats_out                             all
% 59.11/8.00  
% 59.11/8.00  ------ General Options
% 59.11/8.00  
% 59.11/8.00  --fof                                   false
% 59.11/8.00  --time_out_real                         305.
% 59.11/8.00  --time_out_virtual                      -1.
% 59.11/8.00  --symbol_type_check                     false
% 59.11/8.00  --clausify_out                          false
% 59.11/8.00  --sig_cnt_out                           false
% 59.11/8.00  --trig_cnt_out                          false
% 59.11/8.00  --trig_cnt_out_tolerance                1.
% 59.11/8.00  --trig_cnt_out_sk_spl                   false
% 59.11/8.00  --abstr_cl_out                          false
% 59.11/8.00  
% 59.11/8.00  ------ Global Options
% 59.11/8.00  
% 59.11/8.00  --schedule                              default
% 59.11/8.00  --add_important_lit                     false
% 59.11/8.00  --prop_solver_per_cl                    1000
% 59.11/8.00  --min_unsat_core                        false
% 59.11/8.00  --soft_assumptions                      false
% 59.11/8.00  --soft_lemma_size                       3
% 59.11/8.00  --prop_impl_unit_size                   0
% 59.11/8.00  --prop_impl_unit                        []
% 59.11/8.00  --share_sel_clauses                     true
% 59.11/8.00  --reset_solvers                         false
% 59.11/8.00  --bc_imp_inh                            [conj_cone]
% 59.11/8.00  --conj_cone_tolerance                   3.
% 59.11/8.00  --extra_neg_conj                        none
% 59.11/8.00  --large_theory_mode                     true
% 59.11/8.00  --prolific_symb_bound                   200
% 59.11/8.00  --lt_threshold                          2000
% 59.11/8.00  --clause_weak_htbl                      true
% 59.11/8.00  --gc_record_bc_elim                     false
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing Options
% 59.11/8.00  
% 59.11/8.00  --preprocessing_flag                    true
% 59.11/8.00  --time_out_prep_mult                    0.1
% 59.11/8.00  --splitting_mode                        input
% 59.11/8.00  --splitting_grd                         true
% 59.11/8.00  --splitting_cvd                         false
% 59.11/8.00  --splitting_cvd_svl                     false
% 59.11/8.00  --splitting_nvd                         32
% 59.11/8.00  --sub_typing                            true
% 59.11/8.00  --prep_gs_sim                           true
% 59.11/8.00  --prep_unflatten                        true
% 59.11/8.00  --prep_res_sim                          true
% 59.11/8.00  --prep_upred                            true
% 59.11/8.00  --prep_sem_filter                       exhaustive
% 59.11/8.00  --prep_sem_filter_out                   false
% 59.11/8.00  --pred_elim                             true
% 59.11/8.00  --res_sim_input                         true
% 59.11/8.00  --eq_ax_congr_red                       true
% 59.11/8.00  --pure_diseq_elim                       true
% 59.11/8.00  --brand_transform                       false
% 59.11/8.00  --non_eq_to_eq                          false
% 59.11/8.00  --prep_def_merge                        true
% 59.11/8.00  --prep_def_merge_prop_impl              false
% 59.11/8.00  --prep_def_merge_mbd                    true
% 59.11/8.00  --prep_def_merge_tr_red                 false
% 59.11/8.00  --prep_def_merge_tr_cl                  false
% 59.11/8.00  --smt_preprocessing                     true
% 59.11/8.00  --smt_ac_axioms                         fast
% 59.11/8.00  --preprocessed_out                      false
% 59.11/8.00  --preprocessed_stats                    false
% 59.11/8.00  
% 59.11/8.00  ------ Abstraction refinement Options
% 59.11/8.00  
% 59.11/8.00  --abstr_ref                             []
% 59.11/8.00  --abstr_ref_prep                        false
% 59.11/8.00  --abstr_ref_until_sat                   false
% 59.11/8.00  --abstr_ref_sig_restrict                funpre
% 59.11/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 59.11/8.00  --abstr_ref_under                       []
% 59.11/8.00  
% 59.11/8.00  ------ SAT Options
% 59.11/8.00  
% 59.11/8.00  --sat_mode                              false
% 59.11/8.00  --sat_fm_restart_options                ""
% 59.11/8.00  --sat_gr_def                            false
% 59.11/8.00  --sat_epr_types                         true
% 59.11/8.00  --sat_non_cyclic_types                  false
% 59.11/8.00  --sat_finite_models                     false
% 59.11/8.00  --sat_fm_lemmas                         false
% 59.11/8.00  --sat_fm_prep                           false
% 59.11/8.00  --sat_fm_uc_incr                        true
% 59.11/8.00  --sat_out_model                         small
% 59.11/8.00  --sat_out_clauses                       false
% 59.11/8.00  
% 59.11/8.00  ------ QBF Options
% 59.11/8.00  
% 59.11/8.00  --qbf_mode                              false
% 59.11/8.00  --qbf_elim_univ                         false
% 59.11/8.00  --qbf_dom_inst                          none
% 59.11/8.00  --qbf_dom_pre_inst                      false
% 59.11/8.00  --qbf_sk_in                             false
% 59.11/8.00  --qbf_pred_elim                         true
% 59.11/8.00  --qbf_split                             512
% 59.11/8.00  
% 59.11/8.00  ------ BMC1 Options
% 59.11/8.00  
% 59.11/8.00  --bmc1_incremental                      false
% 59.11/8.00  --bmc1_axioms                           reachable_all
% 59.11/8.00  --bmc1_min_bound                        0
% 59.11/8.00  --bmc1_max_bound                        -1
% 59.11/8.00  --bmc1_max_bound_default                -1
% 59.11/8.00  --bmc1_symbol_reachability              true
% 59.11/8.00  --bmc1_property_lemmas                  false
% 59.11/8.00  --bmc1_k_induction                      false
% 59.11/8.00  --bmc1_non_equiv_states                 false
% 59.11/8.00  --bmc1_deadlock                         false
% 59.11/8.00  --bmc1_ucm                              false
% 59.11/8.00  --bmc1_add_unsat_core                   none
% 59.11/8.00  --bmc1_unsat_core_children              false
% 59.11/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 59.11/8.00  --bmc1_out_stat                         full
% 59.11/8.00  --bmc1_ground_init                      false
% 59.11/8.00  --bmc1_pre_inst_next_state              false
% 59.11/8.00  --bmc1_pre_inst_state                   false
% 59.11/8.00  --bmc1_pre_inst_reach_state             false
% 59.11/8.00  --bmc1_out_unsat_core                   false
% 59.11/8.00  --bmc1_aig_witness_out                  false
% 59.11/8.00  --bmc1_verbose                          false
% 59.11/8.00  --bmc1_dump_clauses_tptp                false
% 59.11/8.00  --bmc1_dump_unsat_core_tptp             false
% 59.11/8.00  --bmc1_dump_file                        -
% 59.11/8.00  --bmc1_ucm_expand_uc_limit              128
% 59.11/8.00  --bmc1_ucm_n_expand_iterations          6
% 59.11/8.00  --bmc1_ucm_extend_mode                  1
% 59.11/8.00  --bmc1_ucm_init_mode                    2
% 59.11/8.00  --bmc1_ucm_cone_mode                    none
% 59.11/8.00  --bmc1_ucm_reduced_relation_type        0
% 59.11/8.00  --bmc1_ucm_relax_model                  4
% 59.11/8.00  --bmc1_ucm_full_tr_after_sat            true
% 59.11/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 59.11/8.00  --bmc1_ucm_layered_model                none
% 59.11/8.00  --bmc1_ucm_max_lemma_size               10
% 59.11/8.00  
% 59.11/8.00  ------ AIG Options
% 59.11/8.00  
% 59.11/8.00  --aig_mode                              false
% 59.11/8.00  
% 59.11/8.00  ------ Instantiation Options
% 59.11/8.00  
% 59.11/8.00  --instantiation_flag                    true
% 59.11/8.00  --inst_sos_flag                         false
% 59.11/8.00  --inst_sos_phase                        true
% 59.11/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.11/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.11/8.00  --inst_lit_sel_side                     num_symb
% 59.11/8.00  --inst_solver_per_active                1400
% 59.11/8.00  --inst_solver_calls_frac                1.
% 59.11/8.00  --inst_passive_queue_type               priority_queues
% 59.11/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.11/8.00  --inst_passive_queues_freq              [25;2]
% 59.11/8.00  --inst_dismatching                      true
% 59.11/8.00  --inst_eager_unprocessed_to_passive     true
% 59.11/8.00  --inst_prop_sim_given                   true
% 59.11/8.00  --inst_prop_sim_new                     false
% 59.11/8.00  --inst_subs_new                         false
% 59.11/8.00  --inst_eq_res_simp                      false
% 59.11/8.00  --inst_subs_given                       false
% 59.11/8.00  --inst_orphan_elimination               true
% 59.11/8.00  --inst_learning_loop_flag               true
% 59.11/8.00  --inst_learning_start                   3000
% 59.11/8.00  --inst_learning_factor                  2
% 59.11/8.00  --inst_start_prop_sim_after_learn       3
% 59.11/8.00  --inst_sel_renew                        solver
% 59.11/8.00  --inst_lit_activity_flag                true
% 59.11/8.00  --inst_restr_to_given                   false
% 59.11/8.00  --inst_activity_threshold               500
% 59.11/8.00  --inst_out_proof                        true
% 59.11/8.00  
% 59.11/8.00  ------ Resolution Options
% 59.11/8.00  
% 59.11/8.00  --resolution_flag                       true
% 59.11/8.00  --res_lit_sel                           adaptive
% 59.11/8.00  --res_lit_sel_side                      none
% 59.11/8.00  --res_ordering                          kbo
% 59.11/8.00  --res_to_prop_solver                    active
% 59.11/8.00  --res_prop_simpl_new                    false
% 59.11/8.00  --res_prop_simpl_given                  true
% 59.11/8.00  --res_passive_queue_type                priority_queues
% 59.11/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.11/8.00  --res_passive_queues_freq               [15;5]
% 59.11/8.00  --res_forward_subs                      full
% 59.11/8.00  --res_backward_subs                     full
% 59.11/8.00  --res_forward_subs_resolution           true
% 59.11/8.00  --res_backward_subs_resolution          true
% 59.11/8.00  --res_orphan_elimination                true
% 59.11/8.00  --res_time_limit                        2.
% 59.11/8.00  --res_out_proof                         true
% 59.11/8.00  
% 59.11/8.00  ------ Superposition Options
% 59.11/8.00  
% 59.11/8.00  --superposition_flag                    true
% 59.11/8.00  --sup_passive_queue_type                priority_queues
% 59.11/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.11/8.00  --sup_passive_queues_freq               [8;1;4]
% 59.11/8.00  --demod_completeness_check              fast
% 59.11/8.00  --demod_use_ground                      true
% 59.11/8.00  --sup_to_prop_solver                    passive
% 59.11/8.00  --sup_prop_simpl_new                    true
% 59.11/8.00  --sup_prop_simpl_given                  true
% 59.11/8.00  --sup_fun_splitting                     false
% 59.11/8.00  --sup_smt_interval                      50000
% 59.11/8.00  
% 59.11/8.00  ------ Superposition Simplification Setup
% 59.11/8.00  
% 59.11/8.00  --sup_indices_passive                   []
% 59.11/8.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 59.11/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_full_bw                           [BwDemod]
% 59.11/8.00  --sup_immed_triv                        [TrivRules]
% 59.11/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.11/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_immed_bw_main                     []
% 59.11/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.11/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 59.11/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.11/8.00  
% 59.11/8.00  ------ Combination Options
% 59.11/8.00  
% 59.11/8.00  --comb_res_mult                         3
% 59.11/8.00  --comb_sup_mult                         2
% 59.11/8.00  --comb_inst_mult                        10
% 59.11/8.00  
% 59.11/8.00  ------ Debug Options
% 59.11/8.00  
% 59.11/8.00  --dbg_backtrace                         false
% 59.11/8.00  --dbg_dump_prop_clauses                 false
% 59.11/8.00  --dbg_dump_prop_clauses_file            -
% 59.11/8.00  --dbg_out_stat                          false
% 59.11/8.00  ------ Parsing...
% 59.11/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.11/8.00  ------ Proving...
% 59.11/8.00  ------ Problem Properties 
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  clauses                                 54
% 59.11/8.00  conjectures                             11
% 59.11/8.00  EPR                                     9
% 59.11/8.00  Horn                                    54
% 59.11/8.00  unary                                   20
% 59.11/8.00  binary                                  8
% 59.11/8.00  lits                                    154
% 59.11/8.00  lits eq                                 34
% 59.11/8.00  fd_pure                                 0
% 59.11/8.00  fd_pseudo                               0
% 59.11/8.00  fd_cond                                 0
% 59.11/8.00  fd_pseudo_cond                          2
% 59.11/8.00  AC symbols                              0
% 59.11/8.00  
% 59.11/8.00  ------ Schedule dynamic 5 is on 
% 59.11/8.00  
% 59.11/8.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  ------ 
% 59.11/8.00  Current options:
% 59.11/8.00  ------ 
% 59.11/8.00  
% 59.11/8.00  ------ Input Options
% 59.11/8.00  
% 59.11/8.00  --out_options                           all
% 59.11/8.00  --tptp_safe_out                         true
% 59.11/8.00  --problem_path                          ""
% 59.11/8.00  --include_path                          ""
% 59.11/8.00  --clausifier                            res/vclausify_rel
% 59.11/8.00  --clausifier_options                    --mode clausify
% 59.11/8.00  --stdin                                 false
% 59.11/8.00  --stats_out                             all
% 59.11/8.00  
% 59.11/8.00  ------ General Options
% 59.11/8.00  
% 59.11/8.00  --fof                                   false
% 59.11/8.00  --time_out_real                         305.
% 59.11/8.00  --time_out_virtual                      -1.
% 59.11/8.00  --symbol_type_check                     false
% 59.11/8.00  --clausify_out                          false
% 59.11/8.00  --sig_cnt_out                           false
% 59.11/8.00  --trig_cnt_out                          false
% 59.11/8.00  --trig_cnt_out_tolerance                1.
% 59.11/8.00  --trig_cnt_out_sk_spl                   false
% 59.11/8.00  --abstr_cl_out                          false
% 59.11/8.00  
% 59.11/8.00  ------ Global Options
% 59.11/8.00  
% 59.11/8.00  --schedule                              default
% 59.11/8.00  --add_important_lit                     false
% 59.11/8.00  --prop_solver_per_cl                    1000
% 59.11/8.00  --min_unsat_core                        false
% 59.11/8.00  --soft_assumptions                      false
% 59.11/8.00  --soft_lemma_size                       3
% 59.11/8.00  --prop_impl_unit_size                   0
% 59.11/8.00  --prop_impl_unit                        []
% 59.11/8.00  --share_sel_clauses                     true
% 59.11/8.00  --reset_solvers                         false
% 59.11/8.00  --bc_imp_inh                            [conj_cone]
% 59.11/8.00  --conj_cone_tolerance                   3.
% 59.11/8.00  --extra_neg_conj                        none
% 59.11/8.00  --large_theory_mode                     true
% 59.11/8.00  --prolific_symb_bound                   200
% 59.11/8.00  --lt_threshold                          2000
% 59.11/8.00  --clause_weak_htbl                      true
% 59.11/8.00  --gc_record_bc_elim                     false
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing Options
% 59.11/8.00  
% 59.11/8.00  --preprocessing_flag                    true
% 59.11/8.00  --time_out_prep_mult                    0.1
% 59.11/8.00  --splitting_mode                        input
% 59.11/8.00  --splitting_grd                         true
% 59.11/8.00  --splitting_cvd                         false
% 59.11/8.00  --splitting_cvd_svl                     false
% 59.11/8.00  --splitting_nvd                         32
% 59.11/8.00  --sub_typing                            true
% 59.11/8.00  --prep_gs_sim                           true
% 59.11/8.00  --prep_unflatten                        true
% 59.11/8.00  --prep_res_sim                          true
% 59.11/8.00  --prep_upred                            true
% 59.11/8.00  --prep_sem_filter                       exhaustive
% 59.11/8.00  --prep_sem_filter_out                   false
% 59.11/8.00  --pred_elim                             true
% 59.11/8.00  --res_sim_input                         true
% 59.11/8.00  --eq_ax_congr_red                       true
% 59.11/8.00  --pure_diseq_elim                       true
% 59.11/8.00  --brand_transform                       false
% 59.11/8.00  --non_eq_to_eq                          false
% 59.11/8.00  --prep_def_merge                        true
% 59.11/8.00  --prep_def_merge_prop_impl              false
% 59.11/8.00  --prep_def_merge_mbd                    true
% 59.11/8.00  --prep_def_merge_tr_red                 false
% 59.11/8.00  --prep_def_merge_tr_cl                  false
% 59.11/8.00  --smt_preprocessing                     true
% 59.11/8.00  --smt_ac_axioms                         fast
% 59.11/8.00  --preprocessed_out                      false
% 59.11/8.00  --preprocessed_stats                    false
% 59.11/8.00  
% 59.11/8.00  ------ Abstraction refinement Options
% 59.11/8.00  
% 59.11/8.00  --abstr_ref                             []
% 59.11/8.00  --abstr_ref_prep                        false
% 59.11/8.00  --abstr_ref_until_sat                   false
% 59.11/8.00  --abstr_ref_sig_restrict                funpre
% 59.11/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 59.11/8.00  --abstr_ref_under                       []
% 59.11/8.00  
% 59.11/8.00  ------ SAT Options
% 59.11/8.00  
% 59.11/8.00  --sat_mode                              false
% 59.11/8.00  --sat_fm_restart_options                ""
% 59.11/8.00  --sat_gr_def                            false
% 59.11/8.00  --sat_epr_types                         true
% 59.11/8.00  --sat_non_cyclic_types                  false
% 59.11/8.00  --sat_finite_models                     false
% 59.11/8.00  --sat_fm_lemmas                         false
% 59.11/8.00  --sat_fm_prep                           false
% 59.11/8.00  --sat_fm_uc_incr                        true
% 59.11/8.00  --sat_out_model                         small
% 59.11/8.00  --sat_out_clauses                       false
% 59.11/8.00  
% 59.11/8.00  ------ QBF Options
% 59.11/8.00  
% 59.11/8.00  --qbf_mode                              false
% 59.11/8.00  --qbf_elim_univ                         false
% 59.11/8.00  --qbf_dom_inst                          none
% 59.11/8.00  --qbf_dom_pre_inst                      false
% 59.11/8.00  --qbf_sk_in                             false
% 59.11/8.00  --qbf_pred_elim                         true
% 59.11/8.00  --qbf_split                             512
% 59.11/8.00  
% 59.11/8.00  ------ BMC1 Options
% 59.11/8.00  
% 59.11/8.00  --bmc1_incremental                      false
% 59.11/8.00  --bmc1_axioms                           reachable_all
% 59.11/8.00  --bmc1_min_bound                        0
% 59.11/8.00  --bmc1_max_bound                        -1
% 59.11/8.00  --bmc1_max_bound_default                -1
% 59.11/8.00  --bmc1_symbol_reachability              true
% 59.11/8.00  --bmc1_property_lemmas                  false
% 59.11/8.00  --bmc1_k_induction                      false
% 59.11/8.00  --bmc1_non_equiv_states                 false
% 59.11/8.00  --bmc1_deadlock                         false
% 59.11/8.00  --bmc1_ucm                              false
% 59.11/8.00  --bmc1_add_unsat_core                   none
% 59.11/8.00  --bmc1_unsat_core_children              false
% 59.11/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 59.11/8.00  --bmc1_out_stat                         full
% 59.11/8.00  --bmc1_ground_init                      false
% 59.11/8.00  --bmc1_pre_inst_next_state              false
% 59.11/8.00  --bmc1_pre_inst_state                   false
% 59.11/8.00  --bmc1_pre_inst_reach_state             false
% 59.11/8.00  --bmc1_out_unsat_core                   false
% 59.11/8.00  --bmc1_aig_witness_out                  false
% 59.11/8.00  --bmc1_verbose                          false
% 59.11/8.00  --bmc1_dump_clauses_tptp                false
% 59.11/8.00  --bmc1_dump_unsat_core_tptp             false
% 59.11/8.00  --bmc1_dump_file                        -
% 59.11/8.00  --bmc1_ucm_expand_uc_limit              128
% 59.11/8.00  --bmc1_ucm_n_expand_iterations          6
% 59.11/8.00  --bmc1_ucm_extend_mode                  1
% 59.11/8.00  --bmc1_ucm_init_mode                    2
% 59.11/8.00  --bmc1_ucm_cone_mode                    none
% 59.11/8.00  --bmc1_ucm_reduced_relation_type        0
% 59.11/8.00  --bmc1_ucm_relax_model                  4
% 59.11/8.00  --bmc1_ucm_full_tr_after_sat            true
% 59.11/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 59.11/8.00  --bmc1_ucm_layered_model                none
% 59.11/8.00  --bmc1_ucm_max_lemma_size               10
% 59.11/8.00  
% 59.11/8.00  ------ AIG Options
% 59.11/8.00  
% 59.11/8.00  --aig_mode                              false
% 59.11/8.00  
% 59.11/8.00  ------ Instantiation Options
% 59.11/8.00  
% 59.11/8.00  --instantiation_flag                    true
% 59.11/8.00  --inst_sos_flag                         false
% 59.11/8.00  --inst_sos_phase                        true
% 59.11/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.11/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.11/8.00  --inst_lit_sel_side                     none
% 59.11/8.00  --inst_solver_per_active                1400
% 59.11/8.00  --inst_solver_calls_frac                1.
% 59.11/8.00  --inst_passive_queue_type               priority_queues
% 59.11/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.11/8.00  --inst_passive_queues_freq              [25;2]
% 59.11/8.00  --inst_dismatching                      true
% 59.11/8.00  --inst_eager_unprocessed_to_passive     true
% 59.11/8.00  --inst_prop_sim_given                   true
% 59.11/8.00  --inst_prop_sim_new                     false
% 59.11/8.00  --inst_subs_new                         false
% 59.11/8.00  --inst_eq_res_simp                      false
% 59.11/8.00  --inst_subs_given                       false
% 59.11/8.00  --inst_orphan_elimination               true
% 59.11/8.00  --inst_learning_loop_flag               true
% 59.11/8.00  --inst_learning_start                   3000
% 59.11/8.00  --inst_learning_factor                  2
% 59.11/8.00  --inst_start_prop_sim_after_learn       3
% 59.11/8.00  --inst_sel_renew                        solver
% 59.11/8.00  --inst_lit_activity_flag                true
% 59.11/8.00  --inst_restr_to_given                   false
% 59.11/8.00  --inst_activity_threshold               500
% 59.11/8.00  --inst_out_proof                        true
% 59.11/8.00  
% 59.11/8.00  ------ Resolution Options
% 59.11/8.00  
% 59.11/8.00  --resolution_flag                       false
% 59.11/8.00  --res_lit_sel                           adaptive
% 59.11/8.00  --res_lit_sel_side                      none
% 59.11/8.00  --res_ordering                          kbo
% 59.11/8.00  --res_to_prop_solver                    active
% 59.11/8.00  --res_prop_simpl_new                    false
% 59.11/8.00  --res_prop_simpl_given                  true
% 59.11/8.00  --res_passive_queue_type                priority_queues
% 59.11/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.11/8.00  --res_passive_queues_freq               [15;5]
% 59.11/8.00  --res_forward_subs                      full
% 59.11/8.00  --res_backward_subs                     full
% 59.11/8.00  --res_forward_subs_resolution           true
% 59.11/8.00  --res_backward_subs_resolution          true
% 59.11/8.00  --res_orphan_elimination                true
% 59.11/8.00  --res_time_limit                        2.
% 59.11/8.00  --res_out_proof                         true
% 59.11/8.00  
% 59.11/8.00  ------ Superposition Options
% 59.11/8.00  
% 59.11/8.00  --superposition_flag                    true
% 59.11/8.00  --sup_passive_queue_type                priority_queues
% 59.11/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.11/8.00  --sup_passive_queues_freq               [8;1;4]
% 59.11/8.00  --demod_completeness_check              fast
% 59.11/8.00  --demod_use_ground                      true
% 59.11/8.00  --sup_to_prop_solver                    passive
% 59.11/8.00  --sup_prop_simpl_new                    true
% 59.11/8.00  --sup_prop_simpl_given                  true
% 59.11/8.00  --sup_fun_splitting                     false
% 59.11/8.00  --sup_smt_interval                      50000
% 59.11/8.00  
% 59.11/8.00  ------ Superposition Simplification Setup
% 59.11/8.00  
% 59.11/8.00  --sup_indices_passive                   []
% 59.11/8.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.11/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 59.11/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_full_bw                           [BwDemod]
% 59.11/8.00  --sup_immed_triv                        [TrivRules]
% 59.11/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.11/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_immed_bw_main                     []
% 59.11/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.11/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 59.11/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.11/8.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.11/8.00  
% 59.11/8.00  ------ Combination Options
% 59.11/8.00  
% 59.11/8.00  --comb_res_mult                         3
% 59.11/8.00  --comb_sup_mult                         2
% 59.11/8.00  --comb_inst_mult                        10
% 59.11/8.00  
% 59.11/8.00  ------ Debug Options
% 59.11/8.00  
% 59.11/8.00  --dbg_backtrace                         false
% 59.11/8.00  --dbg_dump_prop_clauses                 false
% 59.11/8.00  --dbg_dump_prop_clauses_file            -
% 59.11/8.00  --dbg_out_stat                          false
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  ------ Proving...
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  % SZS status Theorem for theBenchmark.p
% 59.11/8.00  
% 59.11/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 59.11/8.00  
% 59.11/8.00  fof(f35,conjecture,(
% 59.11/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f36,negated_conjecture,(
% 59.11/8.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.11/8.00    inference(negated_conjecture,[],[f35])).
% 59.11/8.00  
% 59.11/8.00  fof(f81,plain,(
% 59.11/8.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 59.11/8.00    inference(ennf_transformation,[],[f36])).
% 59.11/8.00  
% 59.11/8.00  fof(f82,plain,(
% 59.11/8.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 59.11/8.00    inference(flattening,[],[f81])).
% 59.11/8.00  
% 59.11/8.00  fof(f88,plain,(
% 59.11/8.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 59.11/8.00    introduced(choice_axiom,[])).
% 59.11/8.00  
% 59.11/8.00  fof(f87,plain,(
% 59.11/8.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 59.11/8.00    introduced(choice_axiom,[])).
% 59.11/8.00  
% 59.11/8.00  fof(f89,plain,(
% 59.11/8.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 59.11/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f82,f88,f87])).
% 59.11/8.00  
% 59.11/8.00  fof(f144,plain,(
% 59.11/8.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f27,axiom,(
% 59.11/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f70,plain,(
% 59.11/8.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.11/8.00    inference(ennf_transformation,[],[f27])).
% 59.11/8.00  
% 59.11/8.00  fof(f127,plain,(
% 59.11/8.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f70])).
% 59.11/8.00  
% 59.11/8.00  fof(f33,axiom,(
% 59.11/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f77,plain,(
% 59.11/8.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 59.11/8.00    inference(ennf_transformation,[],[f33])).
% 59.11/8.00  
% 59.11/8.00  fof(f78,plain,(
% 59.11/8.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 59.11/8.00    inference(flattening,[],[f77])).
% 59.11/8.00  
% 59.11/8.00  fof(f135,plain,(
% 59.11/8.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f78])).
% 59.11/8.00  
% 59.11/8.00  fof(f146,plain,(
% 59.11/8.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f139,plain,(
% 59.11/8.00    v1_funct_1(sK2)),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f140,plain,(
% 59.11/8.00    v1_funct_2(sK2,sK0,sK1)),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f141,plain,(
% 59.11/8.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f142,plain,(
% 59.11/8.00    v1_funct_1(sK3)),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f143,plain,(
% 59.11/8.00    v1_funct_2(sK3,sK1,sK0)),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f20,axiom,(
% 59.11/8.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f59,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.11/8.00    inference(ennf_transformation,[],[f20])).
% 59.11/8.00  
% 59.11/8.00  fof(f60,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.11/8.00    inference(flattening,[],[f59])).
% 59.11/8.00  
% 59.11/8.00  fof(f118,plain,(
% 59.11/8.00    ( ! [X0,X1] : (v2_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f60])).
% 59.11/8.00  
% 59.11/8.00  fof(f15,axiom,(
% 59.11/8.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f111,plain,(
% 59.11/8.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f15])).
% 59.11/8.00  
% 59.11/8.00  fof(f32,axiom,(
% 59.11/8.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f134,plain,(
% 59.11/8.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f32])).
% 59.11/8.00  
% 59.11/8.00  fof(f157,plain,(
% 59.11/8.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 59.11/8.00    inference(definition_unfolding,[],[f111,f134])).
% 59.11/8.00  
% 59.11/8.00  fof(f2,axiom,(
% 59.11/8.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f39,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 59.11/8.00    inference(ennf_transformation,[],[f2])).
% 59.11/8.00  
% 59.11/8.00  fof(f93,plain,(
% 59.11/8.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f39])).
% 59.11/8.00  
% 59.11/8.00  fof(f4,axiom,(
% 59.11/8.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f96,plain,(
% 59.11/8.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f4])).
% 59.11/8.00  
% 59.11/8.00  fof(f26,axiom,(
% 59.11/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f38,plain,(
% 59.11/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 59.11/8.00    inference(pure_predicate_removal,[],[f26])).
% 59.11/8.00  
% 59.11/8.00  fof(f69,plain,(
% 59.11/8.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.11/8.00    inference(ennf_transformation,[],[f38])).
% 59.11/8.00  
% 59.11/8.00  fof(f126,plain,(
% 59.11/8.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f69])).
% 59.11/8.00  
% 59.11/8.00  fof(f3,axiom,(
% 59.11/8.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f40,plain,(
% 59.11/8.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.11/8.00    inference(ennf_transformation,[],[f3])).
% 59.11/8.00  
% 59.11/8.00  fof(f85,plain,(
% 59.11/8.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 59.11/8.00    inference(nnf_transformation,[],[f40])).
% 59.11/8.00  
% 59.11/8.00  fof(f94,plain,(
% 59.11/8.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f85])).
% 59.11/8.00  
% 59.11/8.00  fof(f145,plain,(
% 59.11/8.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  fof(f17,axiom,(
% 59.11/8.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f53,plain,(
% 59.11/8.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 59.11/8.00    inference(ennf_transformation,[],[f17])).
% 59.11/8.00  
% 59.11/8.00  fof(f54,plain,(
% 59.11/8.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 59.11/8.00    inference(flattening,[],[f53])).
% 59.11/8.00  
% 59.11/8.00  fof(f115,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f54])).
% 59.11/8.00  
% 59.11/8.00  fof(f9,axiom,(
% 59.11/8.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f45,plain,(
% 59.11/8.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 59.11/8.00    inference(ennf_transformation,[],[f9])).
% 59.11/8.00  
% 59.11/8.00  fof(f46,plain,(
% 59.11/8.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.11/8.00    inference(flattening,[],[f45])).
% 59.11/8.00  
% 59.11/8.00  fof(f101,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f46])).
% 59.11/8.00  
% 59.11/8.00  fof(f6,axiom,(
% 59.11/8.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f42,plain,(
% 59.11/8.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 59.11/8.00    inference(ennf_transformation,[],[f6])).
% 59.11/8.00  
% 59.11/8.00  fof(f98,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f42])).
% 59.11/8.00  
% 59.11/8.00  fof(f31,axiom,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f75,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.11/8.00    inference(ennf_transformation,[],[f31])).
% 59.11/8.00  
% 59.11/8.00  fof(f76,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.11/8.00    inference(flattening,[],[f75])).
% 59.11/8.00  
% 59.11/8.00  fof(f133,plain,(
% 59.11/8.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f76])).
% 59.11/8.00  
% 59.11/8.00  fof(f29,axiom,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f73,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.11/8.00    inference(ennf_transformation,[],[f29])).
% 59.11/8.00  
% 59.11/8.00  fof(f74,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.11/8.00    inference(flattening,[],[f73])).
% 59.11/8.00  
% 59.11/8.00  fof(f131,plain,(
% 59.11/8.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f74])).
% 59.11/8.00  
% 59.11/8.00  fof(f28,axiom,(
% 59.11/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f71,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 59.11/8.00    inference(ennf_transformation,[],[f28])).
% 59.11/8.00  
% 59.11/8.00  fof(f72,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.11/8.00    inference(flattening,[],[f71])).
% 59.11/8.00  
% 59.11/8.00  fof(f86,plain,(
% 59.11/8.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.11/8.00    inference(nnf_transformation,[],[f72])).
% 59.11/8.00  
% 59.11/8.00  fof(f128,plain,(
% 59.11/8.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f86])).
% 59.11/8.00  
% 59.11/8.00  fof(f30,axiom,(
% 59.11/8.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f37,plain,(
% 59.11/8.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 59.11/8.00    inference(pure_predicate_removal,[],[f30])).
% 59.11/8.00  
% 59.11/8.00  fof(f132,plain,(
% 59.11/8.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 59.11/8.00    inference(cnf_transformation,[],[f37])).
% 59.11/8.00  
% 59.11/8.00  fof(f8,axiom,(
% 59.11/8.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f44,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 59.11/8.00    inference(ennf_transformation,[],[f8])).
% 59.11/8.00  
% 59.11/8.00  fof(f100,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f44])).
% 59.11/8.00  
% 59.11/8.00  fof(f10,axiom,(
% 59.11/8.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f102,plain,(
% 59.11/8.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 59.11/8.00    inference(cnf_transformation,[],[f10])).
% 59.11/8.00  
% 59.11/8.00  fof(f152,plain,(
% 59.11/8.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 59.11/8.00    inference(definition_unfolding,[],[f102,f134])).
% 59.11/8.00  
% 59.11/8.00  fof(f119,plain,(
% 59.11/8.00    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f60])).
% 59.11/8.00  
% 59.11/8.00  fof(f23,axiom,(
% 59.11/8.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f65,plain,(
% 59.11/8.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.11/8.00    inference(ennf_transformation,[],[f23])).
% 59.11/8.00  
% 59.11/8.00  fof(f66,plain,(
% 59.11/8.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.11/8.00    inference(flattening,[],[f65])).
% 59.11/8.00  
% 59.11/8.00  fof(f123,plain,(
% 59.11/8.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f66])).
% 59.11/8.00  
% 59.11/8.00  fof(f22,axiom,(
% 59.11/8.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 59.11/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.11/8.00  
% 59.11/8.00  fof(f63,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.11/8.00    inference(ennf_transformation,[],[f22])).
% 59.11/8.00  
% 59.11/8.00  fof(f64,plain,(
% 59.11/8.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.11/8.00    inference(flattening,[],[f63])).
% 59.11/8.00  
% 59.11/8.00  fof(f122,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(cnf_transformation,[],[f64])).
% 59.11/8.00  
% 59.11/8.00  fof(f159,plain,(
% 59.11/8.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.11/8.00    inference(definition_unfolding,[],[f122,f134])).
% 59.11/8.00  
% 59.11/8.00  fof(f150,plain,(
% 59.11/8.00    k2_funct_1(sK2) != sK3),
% 59.11/8.00    inference(cnf_transformation,[],[f89])).
% 59.11/8.00  
% 59.11/8.00  cnf(c_54,negated_conjecture,
% 59.11/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 59.11/8.00      inference(cnf_transformation,[],[f144]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1899,plain,
% 59.11/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_37,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f127]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1907,plain,
% 59.11/8.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 59.11/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4712,plain,
% 59.11/8.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1899,c_1907]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_44,plain,
% 59.11/8.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.11/8.00      | ~ v1_funct_2(X2,X0,X1)
% 59.11/8.00      | ~ v1_funct_2(X3,X1,X0)
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.11/8.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.11/8.00      | ~ v1_funct_1(X2)
% 59.11/8.00      | ~ v1_funct_1(X3)
% 59.11/8.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 59.11/8.00      inference(cnf_transformation,[],[f135]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_52,negated_conjecture,
% 59.11/8.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 59.11/8.00      inference(cnf_transformation,[],[f146]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_686,plain,
% 59.11/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 59.11/8.00      | ~ v1_funct_2(X3,X2,X1)
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 59.11/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X3)
% 59.11/8.00      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 59.11/8.00      | k2_relset_1(X1,X2,X0) = X2
% 59.11/8.00      | k6_partfun1(X2) != k6_partfun1(sK0)
% 59.11/8.00      | sK0 != X2 ),
% 59.11/8.00      inference(resolution_lifted,[status(thm)],[c_44,c_52]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_687,plain,
% 59.11/8.00      ( ~ v1_funct_2(X0,X1,sK0)
% 59.11/8.00      | ~ v1_funct_2(X2,sK0,X1)
% 59.11/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 59.11/8.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X2)
% 59.11/8.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 59.11/8.00      | k2_relset_1(X1,sK0,X0) = sK0
% 59.11/8.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 59.11/8.00      inference(unflattening,[status(thm)],[c_686]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_788,plain,
% 59.11/8.00      ( ~ v1_funct_2(X0,X1,sK0)
% 59.11/8.00      | ~ v1_funct_2(X2,sK0,X1)
% 59.11/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 59.11/8.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X2)
% 59.11/8.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 59.11/8.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 59.11/8.00      inference(equality_resolution_simp,[status(thm)],[c_687]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1891,plain,
% 59.11/8.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 59.11/8.00      | k2_relset_1(X0,sK0,X2) = sK0
% 59.11/8.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 59.11/8.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 59.11/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 59.11/8.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 59.11/8.00      | v1_funct_1(X2) != iProver_top
% 59.11/8.00      | v1_funct_1(X1) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_2597,plain,
% 59.11/8.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 59.11/8.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 59.11/8.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 59.11/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.11/8.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top ),
% 59.11/8.00      inference(equality_resolution,[status(thm)],[c_1891]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_59,negated_conjecture,
% 59.11/8.00      ( v1_funct_1(sK2) ),
% 59.11/8.00      inference(cnf_transformation,[],[f139]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_60,plain,
% 59.11/8.00      ( v1_funct_1(sK2) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_58,negated_conjecture,
% 59.11/8.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 59.11/8.00      inference(cnf_transformation,[],[f140]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_61,plain,
% 59.11/8.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_57,negated_conjecture,
% 59.11/8.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 59.11/8.00      inference(cnf_transformation,[],[f141]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_62,plain,
% 59.11/8.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_56,negated_conjecture,
% 59.11/8.00      ( v1_funct_1(sK3) ),
% 59.11/8.00      inference(cnf_transformation,[],[f142]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_63,plain,
% 59.11/8.00      ( v1_funct_1(sK3) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_55,negated_conjecture,
% 59.11/8.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f143]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_64,plain,
% 59.11/8.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_65,plain,
% 59.11/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_2871,plain,
% 59.11/8.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_2597,c_60,c_61,c_62,c_63,c_64,c_65]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4718,plain,
% 59.11/8.00      ( k2_relat_1(sK3) = sK0 ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_4712,c_2871]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_29,plain,
% 59.11/8.00      ( v2_funct_1(X0)
% 59.11/8.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 59.11/8.00      | ~ v1_funct_1(X1)
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | ~ v1_relat_1(X0)
% 59.11/8.00      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 59.11/8.00      inference(cnf_transformation,[],[f118]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1914,plain,
% 59.11/8.00      ( k2_relat_1(X0) != k1_relat_1(X1)
% 59.11/8.00      | v2_funct_1(X0) = iProver_top
% 59.11/8.00      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_funct_1(X1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X1) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_11658,plain,
% 59.11/8.00      ( k1_relat_1(X0) != sK0
% 59.11/8.00      | v2_funct_1(k5_relat_1(sK3,X0)) != iProver_top
% 59.11/8.00      | v2_funct_1(sK3) = iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_4718,c_1914]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_20,plain,
% 59.11/8.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 59.11/8.00      inference(cnf_transformation,[],[f157]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_143,plain,
% 59.11/8.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_145,plain,
% 59.11/8.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_143]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | v1_relat_1(X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f93]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_2387,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | v1_relat_1(X0)
% 59.11/8.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3258,plain,
% 59.11/8.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 59.11/8.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 59.11/8.00      | v1_relat_1(sK3) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_2387]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3259,plain,
% 59.11/8.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.11/8.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_3258]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_6,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.11/8.00      inference(cnf_transformation,[],[f96]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3695,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3696,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_3695]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_36,plain,
% 59.11/8.00      ( v4_relat_1(X0,X1)
% 59.11/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 59.11/8.00      inference(cnf_transformation,[],[f126]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1908,plain,
% 59.11/8.00      ( v4_relat_1(X0,X1) = iProver_top
% 59.11/8.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4695,plain,
% 59.11/8.00      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1899,c_1908]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_5,plain,
% 59.11/8.00      ( ~ v4_relat_1(X0,X1)
% 59.11/8.00      | r1_tarski(k1_relat_1(X0),X1)
% 59.11/8.00      | ~ v1_relat_1(X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f94]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1933,plain,
% 59.11/8.00      ( v4_relat_1(X0,X1) != iProver_top
% 59.11/8.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1896,plain,
% 59.11/8.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4713,plain,
% 59.11/8.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1896,c_1907]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_53,negated_conjecture,
% 59.11/8.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 59.11/8.00      inference(cnf_transformation,[],[f145]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4715,plain,
% 59.11/8.00      ( k2_relat_1(sK2) = sK1 ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_4713,c_53]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_25,plain,
% 59.11/8.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 59.11/8.00      | ~ v1_funct_1(X1)
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 59.11/8.00      inference(cnf_transformation,[],[f115]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1918,plain,
% 59.11/8.00      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 59.11/8.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12015,plain,
% 59.11/8.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 59.11/8.00      | r1_tarski(X0,sK1) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_4715,c_1918]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3261,plain,
% 59.11/8.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 59.11/8.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 59.11/8.00      | v1_relat_1(sK2) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_2387]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3262,plain,
% 59.11/8.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.11/8.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_3261]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3698,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_3699,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_3698]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12479,plain,
% 59.11/8.00      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 59.11/8.00      | r1_tarski(X0,sK1) != iProver_top ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_12015,c_60,c_62,c_3262,c_3699]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12488,plain,
% 59.11/8.00      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 59.11/8.00      | v4_relat_1(X0,sK1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1933,c_12479]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_14945,plain,
% 59.11/8.00      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_4695,c_12488]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_4696,plain,
% 59.11/8.00      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1896,c_1908]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_11,plain,
% 59.11/8.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 59.11/8.00      inference(cnf_transformation,[],[f101]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1927,plain,
% 59.11/8.00      ( k7_relat_1(X0,X1) = X0
% 59.11/8.00      | v4_relat_1(X0,X1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_6233,plain,
% 59.11/8.00      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_4696,c_1927]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7088,plain,
% 59.11/8.00      ( k7_relat_1(sK2,sK0) = sK2 ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_6233,c_62,c_3262,c_3699]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1935,plain,
% 59.11/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 59.11/8.00      | v1_relat_1(X1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) = iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7260,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) = iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1896,c_1935]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7658,plain,
% 59.11/8.00      ( v1_relat_1(sK2) = iProver_top ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_7260,c_62,c_3262,c_3699]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_8,plain,
% 59.11/8.00      ( ~ v1_relat_1(X0)
% 59.11/8.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 59.11/8.00      inference(cnf_transformation,[],[f98]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1930,plain,
% 59.11/8.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7663,plain,
% 59.11/8.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_7658,c_1930]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_8501,plain,
% 59.11/8.00      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_7088,c_7663]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_8518,plain,
% 59.11/8.00      ( k9_relat_1(sK2,sK0) = sK1 ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_8501,c_4715]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_43,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X3)
% 59.11/8.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f133]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1903,plain,
% 59.11/8.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 59.11/8.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 59.11/8.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.11/8.00      | v1_funct_1(X5) != iProver_top
% 59.11/8.00      | v1_funct_1(X4) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12129,plain,
% 59.11/8.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 59.11/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.11/8.00      | v1_funct_1(X2) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1899,c_1903]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12501,plain,
% 59.11/8.00      ( v1_funct_1(X2) != iProver_top
% 59.11/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.11/8.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_12129,c_63]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12502,plain,
% 59.11/8.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 59.11/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.11/8.00      | v1_funct_1(X2) != iProver_top ),
% 59.11/8.00      inference(renaming,[status(thm)],[c_12501]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12514,plain,
% 59.11/8.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1896,c_12502]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_40,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.11/8.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X3) ),
% 59.11/8.00      inference(cnf_transformation,[],[f131]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1906,plain,
% 59.11/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.11/8.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 59.11/8.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_funct_1(X3) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_39,plain,
% 59.11/8.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 59.11/8.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.11/8.00      | X3 = X2 ),
% 59.11/8.00      inference(cnf_transformation,[],[f128]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_672,plain,
% 59.11/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.11/8.00      | X3 = X0
% 59.11/8.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 59.11/8.00      | k6_partfun1(sK0) != X3
% 59.11/8.00      | sK0 != X2
% 59.11/8.00      | sK0 != X1 ),
% 59.11/8.00      inference(resolution_lifted,[status(thm)],[c_39,c_52]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_673,plain,
% 59.11/8.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 59.11/8.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 59.11/8.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 59.11/8.00      inference(unflattening,[status(thm)],[c_672]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_42,plain,
% 59.11/8.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 59.11/8.00      inference(cnf_transformation,[],[f132]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_82,plain,
% 59.11/8.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 59.11/8.00      inference(instantiation,[status(thm)],[c_42]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_675,plain,
% 59.11/8.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 59.11/8.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_673,c_82]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1892,plain,
% 59.11/8.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 59.11/8.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7980,plain,
% 59.11/8.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 59.11/8.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.11/8.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1906,c_1892]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_11539,plain,
% 59.11/8.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_7980,c_60,c_62,c_63,c_65]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12532,plain,
% 59.11/8.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_12514,c_11539]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13436,plain,
% 59.11/8.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_12532,c_60]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7259,plain,
% 59.11/8.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) = iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_1899,c_1935]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_7518,plain,
% 59.11/8.00      ( v1_relat_1(sK3) = iProver_top ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_7259,c_65,c_3259,c_3696]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_10,plain,
% 59.11/8.00      ( ~ v1_relat_1(X0)
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 59.11/8.00      inference(cnf_transformation,[],[f100]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1928,plain,
% 59.11/8.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 59.11/8.00      | v1_relat_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X1) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_8393,plain,
% 59.11/8.00      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_7658,c_1928]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_9074,plain,
% 59.11/8.00      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_7518,c_8393]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13439,plain,
% 59.11/8.00      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 59.11/8.00      inference(demodulation,[status(thm)],[c_13436,c_9074]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13,plain,
% 59.11/8.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 59.11/8.00      inference(cnf_transformation,[],[f152]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13440,plain,
% 59.11/8.00      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 59.11/8.00      inference(demodulation,[status(thm)],[c_13439,c_13]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_14958,plain,
% 59.11/8.00      ( k1_relat_1(sK3) = sK1 | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(light_normalisation,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_14945,c_8518,c_13440]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_14966,plain,
% 59.11/8.00      ( k1_relat_1(sK3) = sK1 ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_14958,c_65,c_3259,c_3696]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_28,plain,
% 59.11/8.00      ( v2_funct_1(X0)
% 59.11/8.00      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X1)
% 59.11/8.00      | ~ v1_relat_1(X0)
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f119]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1915,plain,
% 59.11/8.00      ( k2_relat_1(X0) != k1_relat_1(X1)
% 59.11/8.00      | v2_funct_1(X1) = iProver_top
% 59.11/8.00      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 59.11/8.00      | v1_funct_1(X1) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_12288,plain,
% 59.11/8.00      ( k1_relat_1(X0) != sK1
% 59.11/8.00      | v2_funct_1(X0) = iProver_top
% 59.11/8.00      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_4715,c_1915]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13020,plain,
% 59.11/8.00      ( v1_relat_1(X0) != iProver_top
% 59.11/8.00      | k1_relat_1(X0) != sK1
% 59.11/8.00      | v2_funct_1(X0) = iProver_top
% 59.11/8.00      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_12288,c_60,c_62,c_3262,c_3699]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13021,plain,
% 59.11/8.00      ( k1_relat_1(X0) != sK1
% 59.11/8.00      | v2_funct_1(X0) = iProver_top
% 59.11/8.00      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(renaming,[status(thm)],[c_13020]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_14985,plain,
% 59.11/8.00      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 59.11/8.00      | v2_funct_1(sK3) = iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_14966,c_13021]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_15014,plain,
% 59.11/8.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 59.11/8.00      | v2_funct_1(sK3) = iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_14985,c_13436]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_123731,plain,
% 59.11/8.00      ( v2_funct_1(sK3) = iProver_top ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_11658,c_63,c_65,c_145,c_3259,c_3696,c_15014]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_33,plain,
% 59.11/8.00      ( ~ v2_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_relat_1(X0)
% 59.11/8.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 59.11/8.00      inference(cnf_transformation,[],[f123]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1910,plain,
% 59.11/8.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 59.11/8.00      | v2_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_123750,plain,
% 59.11/8.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_123731,c_1910]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_32,plain,
% 59.11/8.00      ( ~ v2_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X0)
% 59.11/8.00      | ~ v1_funct_1(X1)
% 59.11/8.00      | ~ v1_relat_1(X0)
% 59.11/8.00      | ~ v1_relat_1(X1)
% 59.11/8.00      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 59.11/8.00      | k2_funct_1(X0) = X1
% 59.11/8.00      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 59.11/8.00      inference(cnf_transformation,[],[f159]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_1911,plain,
% 59.11/8.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 59.11/8.00      | k2_funct_1(X1) = X0
% 59.11/8.00      | k2_relat_1(X0) != k1_relat_1(X1)
% 59.11/8.00      | v2_funct_1(X1) != iProver_top
% 59.11/8.00      | v1_funct_1(X1) != iProver_top
% 59.11/8.00      | v1_funct_1(X0) != iProver_top
% 59.11/8.00      | v1_relat_1(X1) != iProver_top
% 59.11/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.11/8.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13441,plain,
% 59.11/8.00      ( k2_funct_1(sK3) = sK2
% 59.11/8.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 59.11/8.00      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 59.11/8.00      | v2_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(superposition,[status(thm)],[c_13436,c_1911]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13442,plain,
% 59.11/8.00      ( k2_funct_1(sK3) = sK2
% 59.11/8.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 59.11/8.00      | k1_relat_1(sK3) != sK1
% 59.11/8.00      | v2_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(light_normalisation,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_13441,c_4715,c_4718]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_13443,plain,
% 59.11/8.00      ( k2_funct_1(sK3) = sK2
% 59.11/8.00      | k1_relat_1(sK3) != sK1
% 59.11/8.00      | v2_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_funct_1(sK2) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK2) != iProver_top ),
% 59.11/8.00      inference(equality_resolution_simp,[status(thm)],[c_13442]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_17503,plain,
% 59.11/8.00      ( k2_funct_1(sK3) = sK2 ),
% 59.11/8.00      inference(global_propositional_subsumption,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_13443,c_60,c_62,c_63,c_65,c_145,c_3259,c_3262,c_3696,
% 59.11/8.00                 c_3699,c_14958,c_15014]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_123754,plain,
% 59.11/8.00      ( k2_funct_1(sK2) = sK3
% 59.11/8.00      | v1_funct_1(sK3) != iProver_top
% 59.11/8.00      | v1_relat_1(sK3) != iProver_top ),
% 59.11/8.00      inference(light_normalisation,[status(thm)],[c_123750,c_17503]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(c_48,negated_conjecture,
% 59.11/8.00      ( k2_funct_1(sK2) != sK3 ),
% 59.11/8.00      inference(cnf_transformation,[],[f150]) ).
% 59.11/8.00  
% 59.11/8.00  cnf(contradiction,plain,
% 59.11/8.00      ( $false ),
% 59.11/8.00      inference(minisat,
% 59.11/8.00                [status(thm)],
% 59.11/8.00                [c_123754,c_3696,c_3259,c_48,c_65,c_63]) ).
% 59.11/8.00  
% 59.11/8.00  
% 59.11/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 59.11/8.00  
% 59.11/8.00  ------                               Statistics
% 59.11/8.00  
% 59.11/8.00  ------ General
% 59.11/8.00  
% 59.11/8.00  abstr_ref_over_cycles:                  0
% 59.11/8.00  abstr_ref_under_cycles:                 0
% 59.11/8.00  gc_basic_clause_elim:                   0
% 59.11/8.00  forced_gc_time:                         0
% 59.11/8.00  parsing_time:                           0.014
% 59.11/8.00  unif_index_cands_time:                  0.
% 59.11/8.00  unif_index_add_time:                    0.
% 59.11/8.00  orderings_time:                         0.
% 59.11/8.00  out_proof_time:                         0.065
% 59.11/8.00  total_time:                             7.029
% 59.11/8.00  num_of_symbols:                         56
% 59.11/8.00  num_of_terms:                           158916
% 59.11/8.00  
% 59.11/8.00  ------ Preprocessing
% 59.11/8.00  
% 59.11/8.00  num_of_splits:                          0
% 59.11/8.00  num_of_split_atoms:                     0
% 59.11/8.00  num_of_reused_defs:                     0
% 59.11/8.00  num_eq_ax_congr_red:                    12
% 59.11/8.00  num_of_sem_filtered_clauses:            1
% 59.11/8.00  num_of_subtypes:                        0
% 59.11/8.00  monotx_restored_types:                  0
% 59.11/8.00  sat_num_of_epr_types:                   0
% 59.11/8.00  sat_num_of_non_cyclic_types:            0
% 59.11/8.00  sat_guarded_non_collapsed_types:        0
% 59.11/8.00  num_pure_diseq_elim:                    0
% 59.11/8.00  simp_replaced_by:                       0
% 59.11/8.00  res_preprocessed:                       256
% 59.11/8.00  prep_upred:                             0
% 59.11/8.00  prep_unflattend:                        12
% 59.11/8.00  smt_new_axioms:                         0
% 59.11/8.00  pred_elim_cands:                        7
% 59.11/8.00  pred_elim:                              1
% 59.11/8.00  pred_elim_cl:                           1
% 59.11/8.00  pred_elim_cycles:                       4
% 59.11/8.00  merged_defs:                            0
% 59.11/8.00  merged_defs_ncl:                        0
% 59.11/8.00  bin_hyper_res:                          0
% 59.11/8.00  prep_cycles:                            4
% 59.11/8.00  pred_elim_time:                         0.006
% 59.11/8.00  splitting_time:                         0.
% 59.11/8.00  sem_filter_time:                        0.
% 59.11/8.00  monotx_time:                            0.
% 59.11/8.00  subtype_inf_time:                       0.
% 59.11/8.00  
% 59.11/8.00  ------ Problem properties
% 59.11/8.00  
% 59.11/8.00  clauses:                                54
% 59.11/8.00  conjectures:                            11
% 59.11/8.00  epr:                                    9
% 59.11/8.00  horn:                                   54
% 59.11/8.00  ground:                                 12
% 59.11/8.00  unary:                                  20
% 59.11/8.00  binary:                                 8
% 59.11/8.00  lits:                                   154
% 59.11/8.00  lits_eq:                                34
% 59.11/8.00  fd_pure:                                0
% 59.11/8.00  fd_pseudo:                              0
% 59.11/8.00  fd_cond:                                0
% 59.11/8.00  fd_pseudo_cond:                         2
% 59.11/8.00  ac_symbols:                             0
% 59.11/8.00  
% 59.11/8.00  ------ Propositional Solver
% 59.11/8.00  
% 59.11/8.00  prop_solver_calls:                      64
% 59.11/8.00  prop_fast_solver_calls:                 4017
% 59.11/8.00  smt_solver_calls:                       0
% 59.11/8.00  smt_fast_solver_calls:                  0
% 59.11/8.00  prop_num_of_clauses:                    59614
% 59.11/8.00  prop_preprocess_simplified:             104844
% 59.11/8.00  prop_fo_subsumed:                       331
% 59.11/8.00  prop_solver_time:                       0.
% 59.11/8.00  smt_solver_time:                        0.
% 59.11/8.00  smt_fast_solver_time:                   0.
% 59.11/8.00  prop_fast_solver_time:                  0.
% 59.11/8.00  prop_unsat_core_time:                   0.019
% 59.11/8.00  
% 59.11/8.00  ------ QBF
% 59.11/8.00  
% 59.11/8.00  qbf_q_res:                              0
% 59.11/8.00  qbf_num_tautologies:                    0
% 59.11/8.00  qbf_prep_cycles:                        0
% 59.11/8.00  
% 59.11/8.00  ------ BMC1
% 59.11/8.00  
% 59.11/8.00  bmc1_current_bound:                     -1
% 59.11/8.00  bmc1_last_solved_bound:                 -1
% 59.11/8.00  bmc1_unsat_core_size:                   -1
% 59.11/8.00  bmc1_unsat_core_parents_size:           -1
% 59.11/8.00  bmc1_merge_next_fun:                    0
% 59.11/8.00  bmc1_unsat_core_clauses_time:           0.
% 59.11/8.00  
% 59.11/8.00  ------ Instantiation
% 59.11/8.00  
% 59.11/8.00  inst_num_of_clauses:                    1265
% 59.11/8.00  inst_num_in_passive:                    271
% 59.11/8.00  inst_num_in_active:                     2959
% 59.11/8.00  inst_num_in_unprocessed:                629
% 59.11/8.00  inst_num_of_loops:                      3399
% 59.11/8.00  inst_num_of_learning_restarts:          1
% 59.11/8.00  inst_num_moves_active_passive:          439
% 59.11/8.00  inst_lit_activity:                      0
% 59.11/8.00  inst_lit_activity_moves:                9
% 59.11/8.00  inst_num_tautologies:                   0
% 59.11/8.00  inst_num_prop_implied:                  0
% 59.11/8.00  inst_num_existing_simplified:           0
% 59.11/8.01  inst_num_eq_res_simplified:             0
% 59.11/8.01  inst_num_child_elim:                    0
% 59.11/8.01  inst_num_of_dismatching_blockings:      3291
% 59.11/8.01  inst_num_of_non_proper_insts:           11624
% 59.11/8.01  inst_num_of_duplicates:                 0
% 59.11/8.01  inst_inst_num_from_inst_to_res:         0
% 59.11/8.01  inst_dismatching_checking_time:         0.
% 59.11/8.01  
% 59.11/8.01  ------ Resolution
% 59.11/8.01  
% 59.11/8.01  res_num_of_clauses:                     73
% 59.11/8.01  res_num_in_passive:                     73
% 59.11/8.01  res_num_in_active:                      0
% 59.11/8.01  res_num_of_loops:                       260
% 59.11/8.01  res_forward_subset_subsumed:            213
% 59.11/8.01  res_backward_subset_subsumed:           0
% 59.11/8.01  res_forward_subsumed:                   0
% 59.11/8.01  res_backward_subsumed:                  0
% 59.11/8.01  res_forward_subsumption_resolution:     1
% 59.11/8.01  res_backward_subsumption_resolution:    0
% 59.11/8.01  res_clause_to_clause_subsumption:       5622
% 59.11/8.01  res_orphan_elimination:                 0
% 59.11/8.01  res_tautology_del:                      61
% 59.11/8.01  res_num_eq_res_simplified:              1
% 59.11/8.01  res_num_sel_changes:                    0
% 59.11/8.01  res_moves_from_active_to_pass:          0
% 59.11/8.01  
% 59.11/8.01  ------ Superposition
% 59.11/8.01  
% 59.11/8.01  sup_time_total:                         0.
% 59.11/8.01  sup_time_generating:                    0.
% 59.11/8.01  sup_time_sim_full:                      0.
% 59.11/8.01  sup_time_sim_immed:                     0.
% 59.11/8.01  
% 59.11/8.01  sup_num_of_clauses:                     1910
% 59.11/8.01  sup_num_in_active:                      639
% 59.11/8.01  sup_num_in_passive:                     1271
% 59.11/8.01  sup_num_of_loops:                       679
% 59.11/8.01  sup_fw_superposition:                   1619
% 59.11/8.01  sup_bw_superposition:                   945
% 59.11/8.01  sup_immediate_simplified:               937
% 59.11/8.01  sup_given_eliminated:                   0
% 59.11/8.01  comparisons_done:                       0
% 59.11/8.01  comparisons_avoided:                    0
% 59.11/8.01  
% 59.11/8.01  ------ Simplifications
% 59.11/8.01  
% 59.11/8.01  
% 59.11/8.01  sim_fw_subset_subsumed:                 59
% 59.11/8.01  sim_bw_subset_subsumed:                 67
% 59.11/8.01  sim_fw_subsumed:                        118
% 59.11/8.01  sim_bw_subsumed:                        0
% 59.11/8.01  sim_fw_subsumption_res:                 31
% 59.11/8.01  sim_bw_subsumption_res:                 0
% 59.11/8.01  sim_tautology_del:                      36
% 59.11/8.01  sim_eq_tautology_del:                   329
% 59.11/8.01  sim_eq_res_simp:                        12
% 59.11/8.01  sim_fw_demodulated:                     145
% 59.11/8.01  sim_bw_demodulated:                     38
% 59.11/8.01  sim_light_normalised:                   810
% 59.11/8.01  sim_joinable_taut:                      0
% 59.11/8.01  sim_joinable_simp:                      0
% 59.11/8.01  sim_ac_normalised:                      0
% 59.11/8.01  sim_smt_subsumption:                    0
% 59.11/8.01  
%------------------------------------------------------------------------------
