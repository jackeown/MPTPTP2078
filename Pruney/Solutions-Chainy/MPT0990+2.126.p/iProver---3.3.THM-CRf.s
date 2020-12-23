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
% DateTime   : Thu Dec  3 12:03:23 EST 2020

% Result     : Theorem 19.79s
% Output     : CNFRefutation 19.79s
% Verified   : 
% Statistics : Number of formulae       :  224 (1874 expanded)
%              Number of clauses        :  127 ( 664 expanded)
%              Number of leaves         :   26 ( 432 expanded)
%              Depth                    :   24
%              Number of atoms          :  637 (11700 expanded)
%              Number of equality atoms :  295 (4076 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f75,plain,(
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

fof(f74,plain,
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

fof(f76,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f70,f75,f74])).

fof(f123,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f76])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f120,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

fof(f118,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f103,f113])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f124,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f63])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f121,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f125,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f24,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f109,f113])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f131,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f88,f113])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f113])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f91,f113])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f101,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f95,f113])).

fof(f129,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2479,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2483,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3413,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_2483])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_363,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_443,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_363])).

cnf(c_2444,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_9904,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_2444])).

cnf(c_9917,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_9904])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2447,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_3414,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2447,c_2483])).

cnf(c_9905,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_2444])).

cnf(c_9974,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_9905])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2445,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2470,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2475,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6972,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_2475])).

cnf(c_45099,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_6972])).

cnf(c_45436,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45099,c_9974])).

cnf(c_45437,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_45436])).

cnf(c_45447,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9974,c_45437])).

cnf(c_43,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2451,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_25,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2462,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6782,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_2462])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2458,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3900,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2447,c_2458])).

cnf(c_45,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3901,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3900,c_45])).

cnf(c_6783,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6782,c_3901])).

cnf(c_52,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_6987,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6783,c_52])).

cnf(c_10613,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_9974,c_6987])).

cnf(c_45448,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45447,c_10613])).

cnf(c_52228,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_9917,c_45448])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2454,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7549,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_2454])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_55,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_8168,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7549,c_55])).

cnf(c_8169,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8168])).

cnf(c_8179,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2447,c_8169])).

cnf(c_31,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_44,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_690,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_80,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_692,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_80])).

cnf(c_2442,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2545,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3134,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2442,c_51,c_49,c_48,c_46,c_80,c_690,c_2545])).

cnf(c_8182,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8179,c_3134])).

cnf(c_8356,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8182,c_52])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2477,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10603,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9974,c_2477])).

cnf(c_13120,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_9917,c_10603])).

cnf(c_13122,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_13120,c_8356])).

cnf(c_12,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_13123,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_13122,c_12])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2459,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3884,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_2459])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2481,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2467,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6872,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_2467])).

cnf(c_7061,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6872,c_52])).

cnf(c_7062,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7061])).

cnf(c_7067,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | v4_relat_1(X0,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_7062])).

cnf(c_7176,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3884,c_7067])).

cnf(c_13133,plain,
    ( k9_relat_1(sK2,sK0) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13123,c_7176])).

cnf(c_3885,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2447,c_2459])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2476,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4645,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3885,c_2476])).

cnf(c_10619,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_9974,c_4645])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2478,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10604,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_9974,c_2478])).

cnf(c_12157,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_10619,c_10604])).

cnf(c_12158,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_12157,c_3901])).

cnf(c_13134,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13133,c_12158])).

cnf(c_13187,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13134,c_9917,c_9974])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2474,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10577,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_9917,c_2474])).

cnf(c_13193,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_13187,c_10577])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2473,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4443,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_2473])).

cnf(c_16140,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_4443])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2464,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6476,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_2464])).

cnf(c_6583,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6476,c_52])).

cnf(c_10615,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_9974,c_6583])).

cnf(c_16146,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16140,c_10615])).

cnf(c_10606,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_9974,c_2473])).

cnf(c_10621,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_10606,c_3901])).

cnf(c_19,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2468,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13119,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_2468,c_10603])).

cnf(c_13124,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_13119,c_12])).

cnf(c_13464,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_10621,c_13124])).

cnf(c_13189,plain,
    ( k10_relat_1(sK2,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_13187,c_13123])).

cnf(c_13476,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_13464,c_13189])).

cnf(c_16147,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16146,c_13476])).

cnf(c_17829,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16147,c_9974])).

cnf(c_52230,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_52228,c_8356,c_13193,c_17829])).

cnf(c_40,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f129])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52230,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n020.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 18:20:22 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 19.79/2.90  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.79/2.90  
% 19.79/2.90  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.79/2.90  
% 19.79/2.90  ------  iProver source info
% 19.79/2.90  
% 19.79/2.90  git: date: 2020-06-30 10:37:57 +0100
% 19.79/2.90  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.79/2.90  git: non_committed_changes: false
% 19.79/2.90  git: last_make_outside_of_git: false
% 19.79/2.90  
% 19.79/2.90  ------ 
% 19.79/2.90  
% 19.79/2.90  ------ Input Options
% 19.79/2.90  
% 19.79/2.90  --out_options                           all
% 19.79/2.90  --tptp_safe_out                         true
% 19.79/2.90  --problem_path                          ""
% 19.79/2.90  --include_path                          ""
% 19.79/2.90  --clausifier                            res/vclausify_rel
% 19.79/2.90  --clausifier_options                    ""
% 19.79/2.90  --stdin                                 false
% 19.79/2.90  --stats_out                             all
% 19.79/2.90  
% 19.79/2.90  ------ General Options
% 19.79/2.90  
% 19.79/2.90  --fof                                   false
% 19.79/2.90  --time_out_real                         305.
% 19.79/2.90  --time_out_virtual                      -1.
% 19.79/2.90  --symbol_type_check                     false
% 19.79/2.90  --clausify_out                          false
% 19.79/2.90  --sig_cnt_out                           false
% 19.79/2.90  --trig_cnt_out                          false
% 19.79/2.90  --trig_cnt_out_tolerance                1.
% 19.79/2.90  --trig_cnt_out_sk_spl                   false
% 19.79/2.90  --abstr_cl_out                          false
% 19.79/2.90  
% 19.79/2.90  ------ Global Options
% 19.79/2.90  
% 19.79/2.90  --schedule                              default
% 19.79/2.90  --add_important_lit                     false
% 19.79/2.90  --prop_solver_per_cl                    1000
% 19.79/2.90  --min_unsat_core                        false
% 19.79/2.90  --soft_assumptions                      false
% 19.79/2.90  --soft_lemma_size                       3
% 19.79/2.90  --prop_impl_unit_size                   0
% 19.79/2.90  --prop_impl_unit                        []
% 19.79/2.90  --share_sel_clauses                     true
% 19.79/2.90  --reset_solvers                         false
% 19.79/2.90  --bc_imp_inh                            [conj_cone]
% 19.79/2.90  --conj_cone_tolerance                   3.
% 19.79/2.90  --extra_neg_conj                        none
% 19.79/2.90  --large_theory_mode                     true
% 19.79/2.90  --prolific_symb_bound                   200
% 19.79/2.90  --lt_threshold                          2000
% 19.79/2.90  --clause_weak_htbl                      true
% 19.79/2.90  --gc_record_bc_elim                     false
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing Options
% 19.79/2.90  
% 19.79/2.90  --preprocessing_flag                    true
% 19.79/2.90  --time_out_prep_mult                    0.1
% 19.79/2.90  --splitting_mode                        input
% 19.79/2.90  --splitting_grd                         true
% 19.79/2.90  --splitting_cvd                         false
% 19.79/2.90  --splitting_cvd_svl                     false
% 19.79/2.90  --splitting_nvd                         32
% 19.79/2.90  --sub_typing                            true
% 19.79/2.90  --prep_gs_sim                           true
% 19.79/2.90  --prep_unflatten                        true
% 19.79/2.90  --prep_res_sim                          true
% 19.79/2.90  --prep_upred                            true
% 19.79/2.90  --prep_sem_filter                       exhaustive
% 19.79/2.90  --prep_sem_filter_out                   false
% 19.79/2.90  --pred_elim                             true
% 19.79/2.90  --res_sim_input                         true
% 19.79/2.90  --eq_ax_congr_red                       true
% 19.79/2.90  --pure_diseq_elim                       true
% 19.79/2.90  --brand_transform                       false
% 19.79/2.90  --non_eq_to_eq                          false
% 19.79/2.90  --prep_def_merge                        true
% 19.79/2.90  --prep_def_merge_prop_impl              false
% 19.79/2.90  --prep_def_merge_mbd                    true
% 19.79/2.90  --prep_def_merge_tr_red                 false
% 19.79/2.90  --prep_def_merge_tr_cl                  false
% 19.79/2.90  --smt_preprocessing                     true
% 19.79/2.90  --smt_ac_axioms                         fast
% 19.79/2.90  --preprocessed_out                      false
% 19.79/2.90  --preprocessed_stats                    false
% 19.79/2.90  
% 19.79/2.90  ------ Abstraction refinement Options
% 19.79/2.90  
% 19.79/2.90  --abstr_ref                             []
% 19.79/2.90  --abstr_ref_prep                        false
% 19.79/2.90  --abstr_ref_until_sat                   false
% 19.79/2.90  --abstr_ref_sig_restrict                funpre
% 19.79/2.90  --abstr_ref_af_restrict_to_split_sk     false
% 19.79/2.90  --abstr_ref_under                       []
% 19.79/2.90  
% 19.79/2.90  ------ SAT Options
% 19.79/2.90  
% 19.79/2.90  --sat_mode                              false
% 19.79/2.90  --sat_fm_restart_options                ""
% 19.79/2.90  --sat_gr_def                            false
% 19.79/2.90  --sat_epr_types                         true
% 19.79/2.90  --sat_non_cyclic_types                  false
% 19.79/2.90  --sat_finite_models                     false
% 19.79/2.90  --sat_fm_lemmas                         false
% 19.79/2.90  --sat_fm_prep                           false
% 19.79/2.90  --sat_fm_uc_incr                        true
% 19.79/2.90  --sat_out_model                         small
% 19.79/2.90  --sat_out_clauses                       false
% 19.79/2.90  
% 19.79/2.90  ------ QBF Options
% 19.79/2.90  
% 19.79/2.90  --qbf_mode                              false
% 19.79/2.90  --qbf_elim_univ                         false
% 19.79/2.90  --qbf_dom_inst                          none
% 19.79/2.90  --qbf_dom_pre_inst                      false
% 19.79/2.90  --qbf_sk_in                             false
% 19.79/2.90  --qbf_pred_elim                         true
% 19.79/2.90  --qbf_split                             512
% 19.79/2.90  
% 19.79/2.90  ------ BMC1 Options
% 19.79/2.90  
% 19.79/2.90  --bmc1_incremental                      false
% 19.79/2.90  --bmc1_axioms                           reachable_all
% 19.79/2.90  --bmc1_min_bound                        0
% 19.79/2.90  --bmc1_max_bound                        -1
% 19.79/2.90  --bmc1_max_bound_default                -1
% 19.79/2.90  --bmc1_symbol_reachability              true
% 19.79/2.90  --bmc1_property_lemmas                  false
% 19.79/2.90  --bmc1_k_induction                      false
% 19.79/2.90  --bmc1_non_equiv_states                 false
% 19.79/2.90  --bmc1_deadlock                         false
% 19.79/2.90  --bmc1_ucm                              false
% 19.79/2.90  --bmc1_add_unsat_core                   none
% 19.79/2.90  --bmc1_unsat_core_children              false
% 19.79/2.90  --bmc1_unsat_core_extrapolate_axioms    false
% 19.79/2.90  --bmc1_out_stat                         full
% 19.79/2.90  --bmc1_ground_init                      false
% 19.79/2.90  --bmc1_pre_inst_next_state              false
% 19.79/2.90  --bmc1_pre_inst_state                   false
% 19.79/2.90  --bmc1_pre_inst_reach_state             false
% 19.79/2.90  --bmc1_out_unsat_core                   false
% 19.79/2.90  --bmc1_aig_witness_out                  false
% 19.79/2.90  --bmc1_verbose                          false
% 19.79/2.90  --bmc1_dump_clauses_tptp                false
% 19.79/2.90  --bmc1_dump_unsat_core_tptp             false
% 19.79/2.90  --bmc1_dump_file                        -
% 19.79/2.90  --bmc1_ucm_expand_uc_limit              128
% 19.79/2.90  --bmc1_ucm_n_expand_iterations          6
% 19.79/2.90  --bmc1_ucm_extend_mode                  1
% 19.79/2.90  --bmc1_ucm_init_mode                    2
% 19.79/2.90  --bmc1_ucm_cone_mode                    none
% 19.79/2.90  --bmc1_ucm_reduced_relation_type        0
% 19.79/2.90  --bmc1_ucm_relax_model                  4
% 19.79/2.90  --bmc1_ucm_full_tr_after_sat            true
% 19.79/2.90  --bmc1_ucm_expand_neg_assumptions       false
% 19.79/2.90  --bmc1_ucm_layered_model                none
% 19.79/2.90  --bmc1_ucm_max_lemma_size               10
% 19.79/2.90  
% 19.79/2.90  ------ AIG Options
% 19.79/2.90  
% 19.79/2.90  --aig_mode                              false
% 19.79/2.90  
% 19.79/2.90  ------ Instantiation Options
% 19.79/2.90  
% 19.79/2.90  --instantiation_flag                    true
% 19.79/2.90  --inst_sos_flag                         true
% 19.79/2.90  --inst_sos_phase                        true
% 19.79/2.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.79/2.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.79/2.90  --inst_lit_sel_side                     num_symb
% 19.79/2.90  --inst_solver_per_active                1400
% 19.79/2.90  --inst_solver_calls_frac                1.
% 19.79/2.90  --inst_passive_queue_type               priority_queues
% 19.79/2.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.79/2.90  --inst_passive_queues_freq              [25;2]
% 19.79/2.90  --inst_dismatching                      true
% 19.79/2.90  --inst_eager_unprocessed_to_passive     true
% 19.79/2.90  --inst_prop_sim_given                   true
% 19.79/2.90  --inst_prop_sim_new                     false
% 19.79/2.90  --inst_subs_new                         false
% 19.79/2.90  --inst_eq_res_simp                      false
% 19.79/2.90  --inst_subs_given                       false
% 19.79/2.90  --inst_orphan_elimination               true
% 19.79/2.90  --inst_learning_loop_flag               true
% 19.79/2.90  --inst_learning_start                   3000
% 19.79/2.90  --inst_learning_factor                  2
% 19.79/2.90  --inst_start_prop_sim_after_learn       3
% 19.79/2.90  --inst_sel_renew                        solver
% 19.79/2.90  --inst_lit_activity_flag                true
% 19.79/2.90  --inst_restr_to_given                   false
% 19.79/2.90  --inst_activity_threshold               500
% 19.79/2.90  --inst_out_proof                        true
% 19.79/2.90  
% 19.79/2.90  ------ Resolution Options
% 19.79/2.90  
% 19.79/2.90  --resolution_flag                       true
% 19.79/2.90  --res_lit_sel                           adaptive
% 19.79/2.90  --res_lit_sel_side                      none
% 19.79/2.90  --res_ordering                          kbo
% 19.79/2.90  --res_to_prop_solver                    active
% 19.79/2.90  --res_prop_simpl_new                    false
% 19.79/2.90  --res_prop_simpl_given                  true
% 19.79/2.90  --res_passive_queue_type                priority_queues
% 19.79/2.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.79/2.90  --res_passive_queues_freq               [15;5]
% 19.79/2.90  --res_forward_subs                      full
% 19.79/2.90  --res_backward_subs                     full
% 19.79/2.90  --res_forward_subs_resolution           true
% 19.79/2.90  --res_backward_subs_resolution          true
% 19.79/2.90  --res_orphan_elimination                true
% 19.79/2.90  --res_time_limit                        2.
% 19.79/2.90  --res_out_proof                         true
% 19.79/2.90  
% 19.79/2.90  ------ Superposition Options
% 19.79/2.90  
% 19.79/2.90  --superposition_flag                    true
% 19.79/2.90  --sup_passive_queue_type                priority_queues
% 19.79/2.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.79/2.90  --sup_passive_queues_freq               [8;1;4]
% 19.79/2.90  --demod_completeness_check              fast
% 19.79/2.90  --demod_use_ground                      true
% 19.79/2.90  --sup_to_prop_solver                    passive
% 19.79/2.90  --sup_prop_simpl_new                    true
% 19.79/2.90  --sup_prop_simpl_given                  true
% 19.79/2.90  --sup_fun_splitting                     true
% 19.79/2.90  --sup_smt_interval                      50000
% 19.79/2.90  
% 19.79/2.90  ------ Superposition Simplification Setup
% 19.79/2.90  
% 19.79/2.90  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.79/2.90  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.79/2.90  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.79/2.90  --sup_full_triv                         [TrivRules;PropSubs]
% 19.79/2.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.79/2.90  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.79/2.90  --sup_immed_triv                        [TrivRules]
% 19.79/2.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_immed_bw_main                     []
% 19.79/2.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.79/2.90  --sup_input_triv                        [Unflattening;TrivRules]
% 19.79/2.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_input_bw                          []
% 19.79/2.90  
% 19.79/2.90  ------ Combination Options
% 19.79/2.90  
% 19.79/2.90  --comb_res_mult                         3
% 19.79/2.90  --comb_sup_mult                         2
% 19.79/2.90  --comb_inst_mult                        10
% 19.79/2.90  
% 19.79/2.90  ------ Debug Options
% 19.79/2.90  
% 19.79/2.90  --dbg_backtrace                         false
% 19.79/2.90  --dbg_dump_prop_clauses                 false
% 19.79/2.90  --dbg_dump_prop_clauses_file            -
% 19.79/2.90  --dbg_out_stat                          false
% 19.79/2.90  ------ Parsing...
% 19.79/2.90  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.79/2.90  ------ Proving...
% 19.79/2.90  ------ Problem Properties 
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  clauses                                 50
% 19.79/2.90  conjectures                             11
% 19.79/2.90  EPR                                     8
% 19.79/2.90  Horn                                    50
% 19.79/2.90  unary                                   17
% 19.79/2.90  binary                                  9
% 19.79/2.90  lits                                    138
% 19.79/2.90  lits eq                                 28
% 19.79/2.90  fd_pure                                 0
% 19.79/2.90  fd_pseudo                               0
% 19.79/2.90  fd_cond                                 0
% 19.79/2.90  fd_pseudo_cond                          0
% 19.79/2.90  AC symbols                              0
% 19.79/2.90  
% 19.79/2.90  ------ Schedule dynamic 5 is on 
% 19.79/2.90  
% 19.79/2.90  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  ------ 
% 19.79/2.90  Current options:
% 19.79/2.90  ------ 
% 19.79/2.90  
% 19.79/2.90  ------ Input Options
% 19.79/2.90  
% 19.79/2.90  --out_options                           all
% 19.79/2.90  --tptp_safe_out                         true
% 19.79/2.90  --problem_path                          ""
% 19.79/2.90  --include_path                          ""
% 19.79/2.90  --clausifier                            res/vclausify_rel
% 19.79/2.90  --clausifier_options                    ""
% 19.79/2.90  --stdin                                 false
% 19.79/2.90  --stats_out                             all
% 19.79/2.90  
% 19.79/2.90  ------ General Options
% 19.79/2.90  
% 19.79/2.90  --fof                                   false
% 19.79/2.90  --time_out_real                         305.
% 19.79/2.90  --time_out_virtual                      -1.
% 19.79/2.90  --symbol_type_check                     false
% 19.79/2.90  --clausify_out                          false
% 19.79/2.90  --sig_cnt_out                           false
% 19.79/2.90  --trig_cnt_out                          false
% 19.79/2.90  --trig_cnt_out_tolerance                1.
% 19.79/2.90  --trig_cnt_out_sk_spl                   false
% 19.79/2.90  --abstr_cl_out                          false
% 19.79/2.90  
% 19.79/2.90  ------ Global Options
% 19.79/2.90  
% 19.79/2.90  --schedule                              default
% 19.79/2.90  --add_important_lit                     false
% 19.79/2.90  --prop_solver_per_cl                    1000
% 19.79/2.90  --min_unsat_core                        false
% 19.79/2.90  --soft_assumptions                      false
% 19.79/2.90  --soft_lemma_size                       3
% 19.79/2.90  --prop_impl_unit_size                   0
% 19.79/2.90  --prop_impl_unit                        []
% 19.79/2.90  --share_sel_clauses                     true
% 19.79/2.90  --reset_solvers                         false
% 19.79/2.90  --bc_imp_inh                            [conj_cone]
% 19.79/2.90  --conj_cone_tolerance                   3.
% 19.79/2.90  --extra_neg_conj                        none
% 19.79/2.90  --large_theory_mode                     true
% 19.79/2.90  --prolific_symb_bound                   200
% 19.79/2.90  --lt_threshold                          2000
% 19.79/2.90  --clause_weak_htbl                      true
% 19.79/2.90  --gc_record_bc_elim                     false
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing Options
% 19.79/2.90  
% 19.79/2.90  --preprocessing_flag                    true
% 19.79/2.90  --time_out_prep_mult                    0.1
% 19.79/2.90  --splitting_mode                        input
% 19.79/2.90  --splitting_grd                         true
% 19.79/2.90  --splitting_cvd                         false
% 19.79/2.90  --splitting_cvd_svl                     false
% 19.79/2.90  --splitting_nvd                         32
% 19.79/2.90  --sub_typing                            true
% 19.79/2.90  --prep_gs_sim                           true
% 19.79/2.90  --prep_unflatten                        true
% 19.79/2.90  --prep_res_sim                          true
% 19.79/2.90  --prep_upred                            true
% 19.79/2.90  --prep_sem_filter                       exhaustive
% 19.79/2.90  --prep_sem_filter_out                   false
% 19.79/2.90  --pred_elim                             true
% 19.79/2.90  --res_sim_input                         true
% 19.79/2.90  --eq_ax_congr_red                       true
% 19.79/2.90  --pure_diseq_elim                       true
% 19.79/2.90  --brand_transform                       false
% 19.79/2.90  --non_eq_to_eq                          false
% 19.79/2.90  --prep_def_merge                        true
% 19.79/2.90  --prep_def_merge_prop_impl              false
% 19.79/2.90  --prep_def_merge_mbd                    true
% 19.79/2.90  --prep_def_merge_tr_red                 false
% 19.79/2.90  --prep_def_merge_tr_cl                  false
% 19.79/2.90  --smt_preprocessing                     true
% 19.79/2.90  --smt_ac_axioms                         fast
% 19.79/2.90  --preprocessed_out                      false
% 19.79/2.90  --preprocessed_stats                    false
% 19.79/2.90  
% 19.79/2.90  ------ Abstraction refinement Options
% 19.79/2.90  
% 19.79/2.90  --abstr_ref                             []
% 19.79/2.90  --abstr_ref_prep                        false
% 19.79/2.90  --abstr_ref_until_sat                   false
% 19.79/2.90  --abstr_ref_sig_restrict                funpre
% 19.79/2.90  --abstr_ref_af_restrict_to_split_sk     false
% 19.79/2.90  --abstr_ref_under                       []
% 19.79/2.90  
% 19.79/2.90  ------ SAT Options
% 19.79/2.90  
% 19.79/2.90  --sat_mode                              false
% 19.79/2.90  --sat_fm_restart_options                ""
% 19.79/2.90  --sat_gr_def                            false
% 19.79/2.90  --sat_epr_types                         true
% 19.79/2.90  --sat_non_cyclic_types                  false
% 19.79/2.90  --sat_finite_models                     false
% 19.79/2.90  --sat_fm_lemmas                         false
% 19.79/2.90  --sat_fm_prep                           false
% 19.79/2.90  --sat_fm_uc_incr                        true
% 19.79/2.90  --sat_out_model                         small
% 19.79/2.90  --sat_out_clauses                       false
% 19.79/2.90  
% 19.79/2.90  ------ QBF Options
% 19.79/2.90  
% 19.79/2.90  --qbf_mode                              false
% 19.79/2.90  --qbf_elim_univ                         false
% 19.79/2.90  --qbf_dom_inst                          none
% 19.79/2.90  --qbf_dom_pre_inst                      false
% 19.79/2.90  --qbf_sk_in                             false
% 19.79/2.90  --qbf_pred_elim                         true
% 19.79/2.90  --qbf_split                             512
% 19.79/2.90  
% 19.79/2.90  ------ BMC1 Options
% 19.79/2.90  
% 19.79/2.90  --bmc1_incremental                      false
% 19.79/2.90  --bmc1_axioms                           reachable_all
% 19.79/2.90  --bmc1_min_bound                        0
% 19.79/2.90  --bmc1_max_bound                        -1
% 19.79/2.90  --bmc1_max_bound_default                -1
% 19.79/2.90  --bmc1_symbol_reachability              true
% 19.79/2.90  --bmc1_property_lemmas                  false
% 19.79/2.90  --bmc1_k_induction                      false
% 19.79/2.90  --bmc1_non_equiv_states                 false
% 19.79/2.90  --bmc1_deadlock                         false
% 19.79/2.90  --bmc1_ucm                              false
% 19.79/2.90  --bmc1_add_unsat_core                   none
% 19.79/2.90  --bmc1_unsat_core_children              false
% 19.79/2.90  --bmc1_unsat_core_extrapolate_axioms    false
% 19.79/2.90  --bmc1_out_stat                         full
% 19.79/2.90  --bmc1_ground_init                      false
% 19.79/2.90  --bmc1_pre_inst_next_state              false
% 19.79/2.90  --bmc1_pre_inst_state                   false
% 19.79/2.90  --bmc1_pre_inst_reach_state             false
% 19.79/2.90  --bmc1_out_unsat_core                   false
% 19.79/2.90  --bmc1_aig_witness_out                  false
% 19.79/2.90  --bmc1_verbose                          false
% 19.79/2.90  --bmc1_dump_clauses_tptp                false
% 19.79/2.90  --bmc1_dump_unsat_core_tptp             false
% 19.79/2.90  --bmc1_dump_file                        -
% 19.79/2.90  --bmc1_ucm_expand_uc_limit              128
% 19.79/2.90  --bmc1_ucm_n_expand_iterations          6
% 19.79/2.90  --bmc1_ucm_extend_mode                  1
% 19.79/2.90  --bmc1_ucm_init_mode                    2
% 19.79/2.90  --bmc1_ucm_cone_mode                    none
% 19.79/2.90  --bmc1_ucm_reduced_relation_type        0
% 19.79/2.90  --bmc1_ucm_relax_model                  4
% 19.79/2.90  --bmc1_ucm_full_tr_after_sat            true
% 19.79/2.90  --bmc1_ucm_expand_neg_assumptions       false
% 19.79/2.90  --bmc1_ucm_layered_model                none
% 19.79/2.90  --bmc1_ucm_max_lemma_size               10
% 19.79/2.90  
% 19.79/2.90  ------ AIG Options
% 19.79/2.90  
% 19.79/2.90  --aig_mode                              false
% 19.79/2.90  
% 19.79/2.90  ------ Instantiation Options
% 19.79/2.90  
% 19.79/2.90  --instantiation_flag                    true
% 19.79/2.90  --inst_sos_flag                         true
% 19.79/2.90  --inst_sos_phase                        true
% 19.79/2.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.79/2.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.79/2.90  --inst_lit_sel_side                     none
% 19.79/2.90  --inst_solver_per_active                1400
% 19.79/2.90  --inst_solver_calls_frac                1.
% 19.79/2.90  --inst_passive_queue_type               priority_queues
% 19.79/2.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.79/2.90  --inst_passive_queues_freq              [25;2]
% 19.79/2.90  --inst_dismatching                      true
% 19.79/2.90  --inst_eager_unprocessed_to_passive     true
% 19.79/2.90  --inst_prop_sim_given                   true
% 19.79/2.90  --inst_prop_sim_new                     false
% 19.79/2.90  --inst_subs_new                         false
% 19.79/2.90  --inst_eq_res_simp                      false
% 19.79/2.90  --inst_subs_given                       false
% 19.79/2.90  --inst_orphan_elimination               true
% 19.79/2.90  --inst_learning_loop_flag               true
% 19.79/2.90  --inst_learning_start                   3000
% 19.79/2.90  --inst_learning_factor                  2
% 19.79/2.90  --inst_start_prop_sim_after_learn       3
% 19.79/2.90  --inst_sel_renew                        solver
% 19.79/2.90  --inst_lit_activity_flag                true
% 19.79/2.90  --inst_restr_to_given                   false
% 19.79/2.90  --inst_activity_threshold               500
% 19.79/2.90  --inst_out_proof                        true
% 19.79/2.90  
% 19.79/2.90  ------ Resolution Options
% 19.79/2.90  
% 19.79/2.90  --resolution_flag                       false
% 19.79/2.90  --res_lit_sel                           adaptive
% 19.79/2.90  --res_lit_sel_side                      none
% 19.79/2.90  --res_ordering                          kbo
% 19.79/2.90  --res_to_prop_solver                    active
% 19.79/2.90  --res_prop_simpl_new                    false
% 19.79/2.90  --res_prop_simpl_given                  true
% 19.79/2.90  --res_passive_queue_type                priority_queues
% 19.79/2.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.79/2.90  --res_passive_queues_freq               [15;5]
% 19.79/2.90  --res_forward_subs                      full
% 19.79/2.90  --res_backward_subs                     full
% 19.79/2.90  --res_forward_subs_resolution           true
% 19.79/2.90  --res_backward_subs_resolution          true
% 19.79/2.90  --res_orphan_elimination                true
% 19.79/2.90  --res_time_limit                        2.
% 19.79/2.90  --res_out_proof                         true
% 19.79/2.90  
% 19.79/2.90  ------ Superposition Options
% 19.79/2.90  
% 19.79/2.90  --superposition_flag                    true
% 19.79/2.90  --sup_passive_queue_type                priority_queues
% 19.79/2.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.79/2.90  --sup_passive_queues_freq               [8;1;4]
% 19.79/2.90  --demod_completeness_check              fast
% 19.79/2.90  --demod_use_ground                      true
% 19.79/2.90  --sup_to_prop_solver                    passive
% 19.79/2.90  --sup_prop_simpl_new                    true
% 19.79/2.90  --sup_prop_simpl_given                  true
% 19.79/2.90  --sup_fun_splitting                     true
% 19.79/2.90  --sup_smt_interval                      50000
% 19.79/2.90  
% 19.79/2.90  ------ Superposition Simplification Setup
% 19.79/2.90  
% 19.79/2.90  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.79/2.90  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.79/2.90  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.79/2.90  --sup_full_triv                         [TrivRules;PropSubs]
% 19.79/2.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.79/2.90  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.79/2.90  --sup_immed_triv                        [TrivRules]
% 19.79/2.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_immed_bw_main                     []
% 19.79/2.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.79/2.90  --sup_input_triv                        [Unflattening;TrivRules]
% 19.79/2.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.90  --sup_input_bw                          []
% 19.79/2.90  
% 19.79/2.90  ------ Combination Options
% 19.79/2.90  
% 19.79/2.90  --comb_res_mult                         3
% 19.79/2.90  --comb_sup_mult                         2
% 19.79/2.90  --comb_inst_mult                        10
% 19.79/2.90  
% 19.79/2.90  ------ Debug Options
% 19.79/2.90  
% 19.79/2.90  --dbg_backtrace                         false
% 19.79/2.90  --dbg_dump_prop_clauses                 false
% 19.79/2.90  --dbg_dump_prop_clauses_file            -
% 19.79/2.90  --dbg_out_stat                          false
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  ------ Proving...
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  % SZS status Theorem for theBenchmark.p
% 19.79/2.90  
% 19.79/2.90  % SZS output start CNFRefutation for theBenchmark.p
% 19.79/2.90  
% 19.79/2.90  fof(f5,axiom,(
% 19.79/2.90    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f83,plain,(
% 19.79/2.90    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f5])).
% 19.79/2.90  
% 19.79/2.90  fof(f30,conjecture,(
% 19.79/2.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f31,negated_conjecture,(
% 19.79/2.90    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.79/2.90    inference(negated_conjecture,[],[f30])).
% 19.79/2.90  
% 19.79/2.90  fof(f69,plain,(
% 19.79/2.90    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 19.79/2.90    inference(ennf_transformation,[],[f31])).
% 19.79/2.90  
% 19.79/2.90  fof(f70,plain,(
% 19.79/2.90    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 19.79/2.90    inference(flattening,[],[f69])).
% 19.79/2.90  
% 19.79/2.90  fof(f75,plain,(
% 19.79/2.90    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 19.79/2.90    introduced(choice_axiom,[])).
% 19.79/2.90  
% 19.79/2.90  fof(f74,plain,(
% 19.79/2.90    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 19.79/2.90    introduced(choice_axiom,[])).
% 19.79/2.90  
% 19.79/2.90  fof(f76,plain,(
% 19.79/2.90    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 19.79/2.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f70,f75,f74])).
% 19.79/2.90  
% 19.79/2.90  fof(f123,plain,(
% 19.79/2.90    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f1,axiom,(
% 19.79/2.90    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f71,plain,(
% 19.79/2.90    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.79/2.90    inference(nnf_transformation,[],[f1])).
% 19.79/2.90  
% 19.79/2.90  fof(f77,plain,(
% 19.79/2.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f71])).
% 19.79/2.90  
% 19.79/2.90  fof(f2,axiom,(
% 19.79/2.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f33,plain,(
% 19.79/2.90    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(ennf_transformation,[],[f2])).
% 19.79/2.90  
% 19.79/2.90  fof(f79,plain,(
% 19.79/2.90    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f33])).
% 19.79/2.90  
% 19.79/2.90  fof(f78,plain,(
% 19.79/2.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f71])).
% 19.79/2.90  
% 19.79/2.90  fof(f120,plain,(
% 19.79/2.90    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f118,plain,(
% 19.79/2.90    v1_funct_1(sK2)),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f14,axiom,(
% 19.79/2.90    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f45,plain,(
% 19.79/2.90    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.79/2.90    inference(ennf_transformation,[],[f14])).
% 19.79/2.90  
% 19.79/2.90  fof(f46,plain,(
% 19.79/2.90    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(flattening,[],[f45])).
% 19.79/2.90  
% 19.79/2.90  fof(f93,plain,(
% 19.79/2.90    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f46])).
% 19.79/2.90  
% 19.79/2.90  fof(f9,axiom,(
% 19.79/2.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f40,plain,(
% 19.79/2.90    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(ennf_transformation,[],[f9])).
% 19.79/2.90  
% 19.79/2.90  fof(f87,plain,(
% 19.79/2.90    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f40])).
% 19.79/2.90  
% 19.79/2.90  fof(f126,plain,(
% 19.79/2.90    v2_funct_1(sK2)),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f19,axiom,(
% 19.79/2.90    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f53,plain,(
% 19.79/2.90    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.79/2.90    inference(ennf_transformation,[],[f19])).
% 19.79/2.90  
% 19.79/2.90  fof(f54,plain,(
% 19.79/2.90    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(flattening,[],[f53])).
% 19.79/2.90  
% 19.79/2.90  fof(f103,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f54])).
% 19.79/2.90  
% 19.79/2.90  fof(f27,axiom,(
% 19.79/2.90    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f113,plain,(
% 19.79/2.90    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f27])).
% 19.79/2.90  
% 19.79/2.90  fof(f136,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(definition_unfolding,[],[f103,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f22,axiom,(
% 19.79/2.90    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f58,plain,(
% 19.79/2.90    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.79/2.90    inference(ennf_transformation,[],[f22])).
% 19.79/2.90  
% 19.79/2.90  fof(f106,plain,(
% 19.79/2.90    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f58])).
% 19.79/2.90  
% 19.79/2.90  fof(f124,plain,(
% 19.79/2.90    k2_relset_1(sK0,sK1,sK2) = sK1),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f26,axiom,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f63,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.79/2.90    inference(ennf_transformation,[],[f26])).
% 19.79/2.90  
% 19.79/2.90  fof(f64,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.79/2.90    inference(flattening,[],[f63])).
% 19.79/2.90  
% 19.79/2.90  fof(f112,plain,(
% 19.79/2.90    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f64])).
% 19.79/2.90  
% 19.79/2.90  fof(f121,plain,(
% 19.79/2.90    v1_funct_1(sK3)),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f23,axiom,(
% 19.79/2.90    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f59,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.79/2.90    inference(ennf_transformation,[],[f23])).
% 19.79/2.90  
% 19.79/2.90  fof(f60,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.79/2.90    inference(flattening,[],[f59])).
% 19.79/2.90  
% 19.79/2.90  fof(f73,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.79/2.90    inference(nnf_transformation,[],[f60])).
% 19.79/2.90  
% 19.79/2.90  fof(f107,plain,(
% 19.79/2.90    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f73])).
% 19.79/2.90  
% 19.79/2.90  fof(f125,plain,(
% 19.79/2.90    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  fof(f24,axiom,(
% 19.79/2.90    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f109,plain,(
% 19.79/2.90    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f24])).
% 19.79/2.90  
% 19.79/2.90  fof(f138,plain,(
% 19.79/2.90    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 19.79/2.90    inference(definition_unfolding,[],[f109,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f25,axiom,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f61,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.79/2.90    inference(ennf_transformation,[],[f25])).
% 19.79/2.90  
% 19.79/2.90  fof(f62,plain,(
% 19.79/2.90    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.79/2.90    inference(flattening,[],[f61])).
% 19.79/2.90  
% 19.79/2.90  fof(f111,plain,(
% 19.79/2.90    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f62])).
% 19.79/2.90  
% 19.79/2.90  fof(f7,axiom,(
% 19.79/2.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f37,plain,(
% 19.79/2.90    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(ennf_transformation,[],[f7])).
% 19.79/2.90  
% 19.79/2.90  fof(f85,plain,(
% 19.79/2.90    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f37])).
% 19.79/2.90  
% 19.79/2.90  fof(f10,axiom,(
% 19.79/2.90    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f88,plain,(
% 19.79/2.90    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.79/2.90    inference(cnf_transformation,[],[f10])).
% 19.79/2.90  
% 19.79/2.90  fof(f131,plain,(
% 19.79/2.90    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 19.79/2.90    inference(definition_unfolding,[],[f88,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f21,axiom,(
% 19.79/2.90    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f32,plain,(
% 19.79/2.90    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.79/2.90    inference(pure_predicate_removal,[],[f21])).
% 19.79/2.90  
% 19.79/2.90  fof(f57,plain,(
% 19.79/2.90    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.79/2.90    inference(ennf_transformation,[],[f32])).
% 19.79/2.90  
% 19.79/2.90  fof(f105,plain,(
% 19.79/2.90    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f57])).
% 19.79/2.90  
% 19.79/2.90  fof(f3,axiom,(
% 19.79/2.90    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f34,plain,(
% 19.79/2.90    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.79/2.90    inference(ennf_transformation,[],[f3])).
% 19.79/2.90  
% 19.79/2.90  fof(f72,plain,(
% 19.79/2.90    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.79/2.90    inference(nnf_transformation,[],[f34])).
% 19.79/2.90  
% 19.79/2.90  fof(f80,plain,(
% 19.79/2.90    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f72])).
% 19.79/2.90  
% 19.79/2.90  fof(f16,axiom,(
% 19.79/2.90    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f47,plain,(
% 19.79/2.90    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.79/2.90    inference(ennf_transformation,[],[f16])).
% 19.79/2.90  
% 19.79/2.90  fof(f48,plain,(
% 19.79/2.90    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.79/2.90    inference(flattening,[],[f47])).
% 19.79/2.90  
% 19.79/2.90  fof(f97,plain,(
% 19.79/2.90    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f48])).
% 19.79/2.90  
% 19.79/2.90  fof(f8,axiom,(
% 19.79/2.90    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f38,plain,(
% 19.79/2.90    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.79/2.90    inference(ennf_transformation,[],[f8])).
% 19.79/2.90  
% 19.79/2.90  fof(f39,plain,(
% 19.79/2.90    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.79/2.90    inference(flattening,[],[f38])).
% 19.79/2.90  
% 19.79/2.90  fof(f86,plain,(
% 19.79/2.90    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f39])).
% 19.79/2.90  
% 19.79/2.90  fof(f6,axiom,(
% 19.79/2.90    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f36,plain,(
% 19.79/2.90    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.79/2.90    inference(ennf_transformation,[],[f6])).
% 19.79/2.90  
% 19.79/2.90  fof(f84,plain,(
% 19.79/2.90    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f36])).
% 19.79/2.90  
% 19.79/2.90  fof(f11,axiom,(
% 19.79/2.90    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f41,plain,(
% 19.79/2.90    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 19.79/2.90    inference(ennf_transformation,[],[f11])).
% 19.79/2.90  
% 19.79/2.90  fof(f90,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f41])).
% 19.79/2.90  
% 19.79/2.90  fof(f132,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(definition_unfolding,[],[f90,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f12,axiom,(
% 19.79/2.90    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f42,plain,(
% 19.79/2.90    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 19.79/2.90    inference(ennf_transformation,[],[f12])).
% 19.79/2.90  
% 19.79/2.90  fof(f91,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f42])).
% 19.79/2.90  
% 19.79/2.90  fof(f133,plain,(
% 19.79/2.90    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(definition_unfolding,[],[f91,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f18,axiom,(
% 19.79/2.90    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f51,plain,(
% 19.79/2.90    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.79/2.90    inference(ennf_transformation,[],[f18])).
% 19.79/2.90  
% 19.79/2.90  fof(f52,plain,(
% 19.79/2.90    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.79/2.90    inference(flattening,[],[f51])).
% 19.79/2.90  
% 19.79/2.90  fof(f101,plain,(
% 19.79/2.90    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.79/2.90    inference(cnf_transformation,[],[f52])).
% 19.79/2.90  
% 19.79/2.90  fof(f15,axiom,(
% 19.79/2.90    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.79/2.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.79/2.90  
% 19.79/2.90  fof(f95,plain,(
% 19.79/2.90    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.79/2.90    inference(cnf_transformation,[],[f15])).
% 19.79/2.90  
% 19.79/2.90  fof(f135,plain,(
% 19.79/2.90    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 19.79/2.90    inference(definition_unfolding,[],[f95,f113])).
% 19.79/2.90  
% 19.79/2.90  fof(f129,plain,(
% 19.79/2.90    k2_funct_1(sK2) != sK3),
% 19.79/2.90    inference(cnf_transformation,[],[f76])).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6,plain,
% 19.79/2.90      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f83]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2479,plain,
% 19.79/2.90      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_46,negated_conjecture,
% 19.79/2.90      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 19.79/2.90      inference(cnf_transformation,[],[f123]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2450,plain,
% 19.79/2.90      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_1,plain,
% 19.79/2.90      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f77]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2483,plain,
% 19.79/2.90      ( r1_tarski(X0,X1) = iProver_top
% 19.79/2.90      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3413,plain,
% 19.79/2.90      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2450,c_2483]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2,plain,
% 19.79/2.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.79/2.90      | ~ v1_relat_1(X1)
% 19.79/2.90      | v1_relat_1(X0) ),
% 19.79/2.90      inference(cnf_transformation,[],[f79]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_0,plain,
% 19.79/2.90      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f78]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_363,plain,
% 19.79/2.90      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.79/2.90      inference(prop_impl,[status(thm)],[c_0]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_443,plain,
% 19.79/2.90      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 19.79/2.90      inference(bin_hyper_res,[status(thm)],[c_2,c_363]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2444,plain,
% 19.79/2.90      ( r1_tarski(X0,X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_9904,plain,
% 19.79/2.90      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 19.79/2.90      | v1_relat_1(sK3) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_3413,c_2444]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_9917,plain,
% 19.79/2.90      ( v1_relat_1(sK3) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2479,c_9904]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_49,negated_conjecture,
% 19.79/2.90      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.79/2.90      inference(cnf_transformation,[],[f120]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2447,plain,
% 19.79/2.90      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3414,plain,
% 19.79/2.90      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2447,c_2483]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_9905,plain,
% 19.79/2.90      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_3414,c_2444]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_9974,plain,
% 19.79/2.90      ( v1_relat_1(sK2) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2479,c_9905]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_51,negated_conjecture,
% 19.79/2.90      ( v1_funct_1(sK2) ),
% 19.79/2.90      inference(cnf_transformation,[],[f118]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2445,plain,
% 19.79/2.90      ( v1_funct_1(sK2) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_17,plain,
% 19.79/2.90      ( ~ v1_funct_1(X0)
% 19.79/2.90      | ~ v1_relat_1(X0)
% 19.79/2.90      | v1_relat_1(k2_funct_1(X0)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f93]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2470,plain,
% 19.79/2.90      ( v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10,plain,
% 19.79/2.90      ( ~ v1_relat_1(X0)
% 19.79/2.90      | ~ v1_relat_1(X1)
% 19.79/2.90      | ~ v1_relat_1(X2)
% 19.79/2.90      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f87]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2475,plain,
% 19.79/2.90      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X2) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6972,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 19.79/2.90      | v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2470,c_2475]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45099,plain,
% 19.79/2.90      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2445,c_6972]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45436,plain,
% 19.79/2.90      ( v1_relat_1(X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_45099,c_9974]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45437,plain,
% 19.79/2.90      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top ),
% 19.79/2.90      inference(renaming,[status(thm)],[c_45436]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45447,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_45437]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_43,negated_conjecture,
% 19.79/2.90      ( v2_funct_1(sK2) ),
% 19.79/2.90      inference(cnf_transformation,[],[f126]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2451,plain,
% 19.79/2.90      ( v2_funct_1(sK2) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_25,plain,
% 19.79/2.90      ( ~ v2_funct_1(X0)
% 19.79/2.90      | ~ v1_funct_1(X0)
% 19.79/2.90      | ~ v1_relat_1(X0)
% 19.79/2.90      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f136]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2462,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 19.79/2.90      | v2_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6782,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2451,c_2462]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_29,plain,
% 19.79/2.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.79/2.90      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 19.79/2.90      inference(cnf_transformation,[],[f106]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2458,plain,
% 19.79/2.90      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 19.79/2.90      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3900,plain,
% 19.79/2.90      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2447,c_2458]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45,negated_conjecture,
% 19.79/2.90      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 19.79/2.90      inference(cnf_transformation,[],[f124]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3901,plain,
% 19.79/2.90      ( k2_relat_1(sK2) = sK1 ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_3900,c_45]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6783,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_6782,c_3901]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_52,plain,
% 19.79/2.90      ( v1_funct_1(sK2) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6987,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_6783,c_52]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10613,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_6987]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_45448,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_45447,c_10613]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_52228,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9917,c_45448]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_35,plain,
% 19.79/2.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.79/2.90      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 19.79/2.90      | ~ v1_funct_1(X0)
% 19.79/2.90      | ~ v1_funct_1(X3)
% 19.79/2.90      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 19.79/2.90      inference(cnf_transformation,[],[f112]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2454,plain,
% 19.79/2.90      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 19.79/2.90      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 19.79/2.90      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.79/2.90      | v1_funct_1(X5) != iProver_top
% 19.79/2.90      | v1_funct_1(X4) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7549,plain,
% 19.79/2.90      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 19.79/2.90      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.79/2.90      | v1_funct_1(X2) != iProver_top
% 19.79/2.90      | v1_funct_1(sK3) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2450,c_2454]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_48,negated_conjecture,
% 19.79/2.90      ( v1_funct_1(sK3) ),
% 19.79/2.90      inference(cnf_transformation,[],[f121]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_55,plain,
% 19.79/2.90      ( v1_funct_1(sK3) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8168,plain,
% 19.79/2.90      ( v1_funct_1(X2) != iProver_top
% 19.79/2.90      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.79/2.90      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_7549,c_55]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8169,plain,
% 19.79/2.90      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 19.79/2.90      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.79/2.90      | v1_funct_1(X2) != iProver_top ),
% 19.79/2.90      inference(renaming,[status(thm)],[c_8168]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8179,plain,
% 19.79/2.90      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2447,c_8169]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_31,plain,
% 19.79/2.90      ( ~ r2_relset_1(X0,X1,X2,X3)
% 19.79/2.90      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.79/2.90      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.79/2.90      | X3 = X2 ),
% 19.79/2.90      inference(cnf_transformation,[],[f107]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_44,negated_conjecture,
% 19.79/2.90      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f125]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_689,plain,
% 19.79/2.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.79/2.90      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.79/2.90      | X3 = X0
% 19.79/2.90      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 19.79/2.90      | k6_partfun1(sK0) != X3
% 19.79/2.90      | sK0 != X2
% 19.79/2.90      | sK0 != X1 ),
% 19.79/2.90      inference(resolution_lifted,[status(thm)],[c_31,c_44]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_690,plain,
% 19.79/2.90      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.79/2.90      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.79/2.90      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.79/2.90      inference(unflattening,[status(thm)],[c_689]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_32,plain,
% 19.79/2.90      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 19.79/2.90      inference(cnf_transformation,[],[f138]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_80,plain,
% 19.79/2.90      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 19.79/2.90      inference(instantiation,[status(thm)],[c_32]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_692,plain,
% 19.79/2.90      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.79/2.90      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_690,c_80]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2442,plain,
% 19.79/2.90      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.79/2.90      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_33,plain,
% 19.79/2.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.79/2.90      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 19.79/2.90      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.79/2.90      | ~ v1_funct_1(X0)
% 19.79/2.90      | ~ v1_funct_1(X3) ),
% 19.79/2.90      inference(cnf_transformation,[],[f111]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2545,plain,
% 19.79/2.90      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.79/2.90      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 19.79/2.90      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.79/2.90      | ~ v1_funct_1(sK3)
% 19.79/2.90      | ~ v1_funct_1(sK2) ),
% 19.79/2.90      inference(instantiation,[status(thm)],[c_33]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3134,plain,
% 19.79/2.90      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_2442,c_51,c_49,c_48,c_46,c_80,c_690,c_2545]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8182,plain,
% 19.79/2.90      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_8179,c_3134]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8356,plain,
% 19.79/2.90      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_8182,c_52]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_8,plain,
% 19.79/2.90      ( ~ v1_relat_1(X0)
% 19.79/2.90      | ~ v1_relat_1(X1)
% 19.79/2.90      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f85]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2477,plain,
% 19.79/2.90      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X1) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10603,plain,
% 19.79/2.90      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_2477]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13120,plain,
% 19.79/2.90      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9917,c_10603]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13122,plain,
% 19.79/2.90      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_13120,c_8356]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_12,plain,
% 19.79/2.90      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 19.79/2.90      inference(cnf_transformation,[],[f131]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13123,plain,
% 19.79/2.90      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 19.79/2.90      inference(demodulation,[status(thm)],[c_13122,c_12]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_28,plain,
% 19.79/2.90      ( v4_relat_1(X0,X1)
% 19.79/2.90      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.79/2.90      inference(cnf_transformation,[],[f105]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2459,plain,
% 19.79/2.90      ( v4_relat_1(X0,X1) = iProver_top
% 19.79/2.90      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3884,plain,
% 19.79/2.90      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2450,c_2459]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_4,plain,
% 19.79/2.90      ( ~ v4_relat_1(X0,X1)
% 19.79/2.90      | r1_tarski(k1_relat_1(X0),X1)
% 19.79/2.90      | ~ v1_relat_1(X0) ),
% 19.79/2.90      inference(cnf_transformation,[],[f80]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2481,plain,
% 19.79/2.90      ( v4_relat_1(X0,X1) != iProver_top
% 19.79/2.90      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_20,plain,
% 19.79/2.90      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 19.79/2.90      | ~ v1_funct_1(X1)
% 19.79/2.90      | ~ v1_relat_1(X1)
% 19.79/2.90      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 19.79/2.90      inference(cnf_transformation,[],[f97]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2467,plain,
% 19.79/2.90      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 19.79/2.90      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 19.79/2.90      | v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6872,plain,
% 19.79/2.90      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 19.79/2.90      | r1_tarski(X0,sK1) != iProver_top
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_3901,c_2467]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7061,plain,
% 19.79/2.90      ( r1_tarski(X0,sK1) != iProver_top
% 19.79/2.90      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_6872,c_52]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7062,plain,
% 19.79/2.90      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 19.79/2.90      | r1_tarski(X0,sK1) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(renaming,[status(thm)],[c_7061]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7067,plain,
% 19.79/2.90      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 19.79/2.90      | v4_relat_1(X0,sK1) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2481,c_7062]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7176,plain,
% 19.79/2.90      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 19.79/2.90      | v1_relat_1(sK3) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_3884,c_7067]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13133,plain,
% 19.79/2.90      ( k9_relat_1(sK2,sK0) = k1_relat_1(sK3)
% 19.79/2.90      | v1_relat_1(sK3) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(demodulation,[status(thm)],[c_13123,c_7176]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_3885,plain,
% 19.79/2.90      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2447,c_2459]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_9,plain,
% 19.79/2.90      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 19.79/2.90      inference(cnf_transformation,[],[f86]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2476,plain,
% 19.79/2.90      ( k7_relat_1(X0,X1) = X0
% 19.79/2.90      | v4_relat_1(X0,X1) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_4645,plain,
% 19.79/2.90      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_3885,c_2476]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10619,plain,
% 19.79/2.90      ( k7_relat_1(sK2,sK0) = sK2 ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_4645]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_7,plain,
% 19.79/2.90      ( ~ v1_relat_1(X0)
% 19.79/2.90      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.79/2.90      inference(cnf_transformation,[],[f84]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2478,plain,
% 19.79/2.90      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10604,plain,
% 19.79/2.90      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_2478]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_12157,plain,
% 19.79/2.90      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_10619,c_10604]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_12158,plain,
% 19.79/2.90      ( k9_relat_1(sK2,sK0) = sK1 ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_12157,c_3901]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13134,plain,
% 19.79/2.90      ( k1_relat_1(sK3) = sK1
% 19.79/2.90      | v1_relat_1(sK3) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_13133,c_12158]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13187,plain,
% 19.79/2.90      ( k1_relat_1(sK3) = sK1 ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_13134,c_9917,c_9974]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13,plain,
% 19.79/2.90      ( ~ v1_relat_1(X0)
% 19.79/2.90      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 19.79/2.90      inference(cnf_transformation,[],[f132]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2474,plain,
% 19.79/2.90      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10577,plain,
% 19.79/2.90      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9917,c_2474]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13193,plain,
% 19.79/2.90      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 19.79/2.90      inference(demodulation,[status(thm)],[c_13187,c_10577]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_14,plain,
% 19.79/2.90      ( ~ v1_relat_1(X0)
% 19.79/2.90      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 19.79/2.90      inference(cnf_transformation,[],[f133]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2473,plain,
% 19.79/2.90      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_4443,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 19.79/2.90      | v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2470,c_2473]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_16140,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2445,c_4443]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_23,plain,
% 19.79/2.90      ( ~ v2_funct_1(X0)
% 19.79/2.90      | ~ v1_funct_1(X0)
% 19.79/2.90      | ~ v1_relat_1(X0)
% 19.79/2.90      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 19.79/2.90      inference(cnf_transformation,[],[f101]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2464,plain,
% 19.79/2.90      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 19.79/2.90      | v2_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_funct_1(X0) != iProver_top
% 19.79/2.90      | v1_relat_1(X0) != iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6476,plain,
% 19.79/2.90      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 19.79/2.90      | v1_funct_1(sK2) != iProver_top
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2451,c_2464]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_6583,plain,
% 19.79/2.90      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_6476,c_52]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10615,plain,
% 19.79/2.90      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_6583]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_16146,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_16140,c_10615]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10606,plain,
% 19.79/2.90      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_9974,c_2473]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_10621,plain,
% 19.79/2.90      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_10606,c_3901]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_19,plain,
% 19.79/2.90      ( v1_relat_1(k6_partfun1(X0)) ),
% 19.79/2.90      inference(cnf_transformation,[],[f135]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_2468,plain,
% 19.79/2.90      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 19.79/2.90      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13119,plain,
% 19.79/2.90      ( k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_2468,c_10603]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13124,plain,
% 19.79/2.90      ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_13119,c_12]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13464,plain,
% 19.79/2.90      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 19.79/2.90      inference(superposition,[status(thm)],[c_10621,c_13124]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13189,plain,
% 19.79/2.90      ( k10_relat_1(sK2,sK1) = sK0 ),
% 19.79/2.90      inference(demodulation,[status(thm)],[c_13187,c_13123]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_13476,plain,
% 19.79/2.90      ( k1_relat_1(sK2) = sK0 ),
% 19.79/2.90      inference(light_normalisation,[status(thm)],[c_13464,c_13189]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_16147,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 19.79/2.90      | v1_relat_1(sK2) != iProver_top ),
% 19.79/2.90      inference(demodulation,[status(thm)],[c_16146,c_13476]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_17829,plain,
% 19.79/2.90      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 19.79/2.90      inference(global_propositional_subsumption,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_16147,c_9974]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_52230,plain,
% 19.79/2.90      ( k2_funct_1(sK2) = sK3 ),
% 19.79/2.90      inference(light_normalisation,
% 19.79/2.90                [status(thm)],
% 19.79/2.90                [c_52228,c_8356,c_13193,c_17829]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(c_40,negated_conjecture,
% 19.79/2.90      ( k2_funct_1(sK2) != sK3 ),
% 19.79/2.90      inference(cnf_transformation,[],[f129]) ).
% 19.79/2.90  
% 19.79/2.90  cnf(contradiction,plain,
% 19.79/2.90      ( $false ),
% 19.79/2.90      inference(minisat,[status(thm)],[c_52230,c_40]) ).
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  % SZS output end CNFRefutation for theBenchmark.p
% 19.79/2.90  
% 19.79/2.90  ------                               Statistics
% 19.79/2.90  
% 19.79/2.90  ------ General
% 19.79/2.90  
% 19.79/2.90  abstr_ref_over_cycles:                  0
% 19.79/2.90  abstr_ref_under_cycles:                 0
% 19.79/2.90  gc_basic_clause_elim:                   0
% 19.79/2.90  forced_gc_time:                         0
% 19.79/2.90  parsing_time:                           0.016
% 19.79/2.90  unif_index_cands_time:                  0.
% 19.79/2.90  unif_index_add_time:                    0.
% 19.79/2.90  orderings_time:                         0.
% 19.79/2.90  out_proof_time:                         0.04
% 19.79/2.90  total_time:                             2.37
% 19.79/2.90  num_of_symbols:                         56
% 19.79/2.90  num_of_terms:                           74447
% 19.79/2.90  
% 19.79/2.90  ------ Preprocessing
% 19.79/2.90  
% 19.79/2.90  num_of_splits:                          0
% 19.79/2.90  num_of_split_atoms:                     0
% 19.79/2.90  num_of_reused_defs:                     0
% 19.79/2.90  num_eq_ax_congr_red:                    18
% 19.79/2.90  num_of_sem_filtered_clauses:            1
% 19.79/2.90  num_of_subtypes:                        0
% 19.79/2.90  monotx_restored_types:                  0
% 19.79/2.90  sat_num_of_epr_types:                   0
% 19.79/2.90  sat_num_of_non_cyclic_types:            0
% 19.79/2.90  sat_guarded_non_collapsed_types:        0
% 19.79/2.90  num_pure_diseq_elim:                    0
% 19.79/2.90  simp_replaced_by:                       0
% 19.79/2.90  res_preprocessed:                       240
% 19.79/2.90  prep_upred:                             0
% 19.79/2.90  prep_unflattend:                        40
% 19.79/2.90  smt_new_axioms:                         0
% 19.79/2.90  pred_elim_cands:                        7
% 19.79/2.90  pred_elim:                              1
% 19.79/2.90  pred_elim_cl:                           1
% 19.79/2.90  pred_elim_cycles:                       5
% 19.79/2.90  merged_defs:                            8
% 19.79/2.90  merged_defs_ncl:                        0
% 19.79/2.90  bin_hyper_res:                          9
% 19.79/2.90  prep_cycles:                            4
% 19.79/2.90  pred_elim_time:                         0.015
% 19.79/2.90  splitting_time:                         0.
% 19.79/2.90  sem_filter_time:                        0.
% 19.79/2.90  monotx_time:                            0.001
% 19.79/2.90  subtype_inf_time:                       0.
% 19.79/2.90  
% 19.79/2.90  ------ Problem properties
% 19.79/2.90  
% 19.79/2.90  clauses:                                50
% 19.79/2.90  conjectures:                            11
% 19.79/2.90  epr:                                    8
% 19.79/2.90  horn:                                   50
% 19.79/2.90  ground:                                 12
% 19.79/2.90  unary:                                  17
% 19.79/2.90  binary:                                 9
% 19.79/2.90  lits:                                   138
% 19.79/2.90  lits_eq:                                28
% 19.79/2.90  fd_pure:                                0
% 19.79/2.90  fd_pseudo:                              0
% 19.79/2.90  fd_cond:                                0
% 19.79/2.90  fd_pseudo_cond:                         0
% 19.79/2.90  ac_symbols:                             0
% 19.79/2.90  
% 19.79/2.90  ------ Propositional Solver
% 19.79/2.90  
% 19.79/2.90  prop_solver_calls:                      41
% 19.79/2.90  prop_fast_solver_calls:                 3593
% 19.79/2.90  smt_solver_calls:                       0
% 19.79/2.90  smt_fast_solver_calls:                  0
% 19.79/2.90  prop_num_of_clauses:                    29243
% 19.79/2.90  prop_preprocess_simplified:             51269
% 19.79/2.90  prop_fo_subsumed:                       267
% 19.79/2.90  prop_solver_time:                       0.
% 19.79/2.90  smt_solver_time:                        0.
% 19.79/2.90  smt_fast_solver_time:                   0.
% 19.79/2.90  prop_fast_solver_time:                  0.
% 19.79/2.90  prop_unsat_core_time:                   0.006
% 19.79/2.90  
% 19.79/2.90  ------ QBF
% 19.79/2.90  
% 19.79/2.90  qbf_q_res:                              0
% 19.79/2.90  qbf_num_tautologies:                    0
% 19.79/2.90  qbf_prep_cycles:                        0
% 19.79/2.90  
% 19.79/2.90  ------ BMC1
% 19.79/2.90  
% 19.79/2.90  bmc1_current_bound:                     -1
% 19.79/2.90  bmc1_last_solved_bound:                 -1
% 19.79/2.90  bmc1_unsat_core_size:                   -1
% 19.79/2.90  bmc1_unsat_core_parents_size:           -1
% 19.79/2.90  bmc1_merge_next_fun:                    0
% 19.79/2.90  bmc1_unsat_core_clauses_time:           0.
% 19.79/2.90  
% 19.79/2.90  ------ Instantiation
% 19.79/2.90  
% 19.79/2.90  inst_num_of_clauses:                    1360
% 19.79/2.90  inst_num_in_passive:                    277
% 19.79/2.90  inst_num_in_active:                     3205
% 19.79/2.90  inst_num_in_unprocessed:                646
% 19.79/2.90  inst_num_of_loops:                      3439
% 19.79/2.90  inst_num_of_learning_restarts:          1
% 19.79/2.90  inst_num_moves_active_passive:          226
% 19.79/2.90  inst_lit_activity:                      0
% 19.79/2.90  inst_lit_activity_moves:                1
% 19.79/2.90  inst_num_tautologies:                   0
% 19.79/2.90  inst_num_prop_implied:                  0
% 19.79/2.90  inst_num_existing_simplified:           0
% 19.79/2.90  inst_num_eq_res_simplified:             0
% 19.79/2.90  inst_num_child_elim:                    0
% 19.79/2.90  inst_num_of_dismatching_blockings:      2763
% 19.79/2.90  inst_num_of_non_proper_insts:           7022
% 19.79/2.90  inst_num_of_duplicates:                 0
% 19.79/2.90  inst_inst_num_from_inst_to_res:         0
% 19.79/2.90  inst_dismatching_checking_time:         0.
% 19.79/2.90  
% 19.79/2.90  ------ Resolution
% 19.79/2.90  
% 19.79/2.90  res_num_of_clauses:                     69
% 19.79/2.90  res_num_in_passive:                     69
% 19.79/2.90  res_num_in_active:                      0
% 19.79/2.90  res_num_of_loops:                       244
% 19.79/2.90  res_forward_subset_subsumed:            305
% 19.79/2.90  res_backward_subset_subsumed:           0
% 19.79/2.90  res_forward_subsumed:                   0
% 19.79/2.90  res_backward_subsumed:                  0
% 19.79/2.90  res_forward_subsumption_resolution:     1
% 19.79/2.90  res_backward_subsumption_resolution:    0
% 19.79/2.90  res_clause_to_clause_subsumption:       3918
% 19.79/2.90  res_orphan_elimination:                 0
% 19.79/2.90  res_tautology_del:                      261
% 19.79/2.90  res_num_eq_res_simplified:              1
% 19.79/2.90  res_num_sel_changes:                    0
% 19.79/2.90  res_moves_from_active_to_pass:          0
% 19.79/2.90  
% 19.79/2.90  ------ Superposition
% 19.79/2.90  
% 19.79/2.90  sup_time_total:                         0.
% 19.79/2.90  sup_time_generating:                    0.
% 19.79/2.90  sup_time_sim_full:                      0.
% 19.79/2.90  sup_time_sim_immed:                     0.
% 19.79/2.90  
% 19.79/2.90  sup_num_of_clauses:                     1809
% 19.79/2.90  sup_num_in_active:                      606
% 19.79/2.90  sup_num_in_passive:                     1203
% 19.79/2.90  sup_num_of_loops:                       686
% 19.79/2.90  sup_fw_superposition:                   1350
% 19.79/2.90  sup_bw_superposition:                   1133
% 19.79/2.90  sup_immediate_simplified:               716
% 19.79/2.90  sup_given_eliminated:                   1
% 19.79/2.90  comparisons_done:                       0
% 19.79/2.90  comparisons_avoided:                    0
% 19.79/2.90  
% 19.79/2.90  ------ Simplifications
% 19.79/2.90  
% 19.79/2.90  
% 19.79/2.90  sim_fw_subset_subsumed:                 47
% 19.79/2.90  sim_bw_subset_subsumed:                 55
% 19.79/2.90  sim_fw_subsumed:                        176
% 19.79/2.90  sim_bw_subsumed:                        6
% 19.79/2.90  sim_fw_subsumption_res:                 0
% 19.79/2.90  sim_bw_subsumption_res:                 0
% 19.79/2.90  sim_tautology_del:                      31
% 19.79/2.90  sim_eq_tautology_del:                   218
% 19.79/2.90  sim_eq_res_simp:                        1
% 19.79/2.90  sim_fw_demodulated:                     161
% 19.79/2.90  sim_bw_demodulated:                     52
% 19.79/2.90  sim_light_normalised:                   571
% 19.79/2.90  sim_joinable_taut:                      0
% 19.79/2.90  sim_joinable_simp:                      0
% 19.79/2.90  sim_ac_normalised:                      0
% 19.79/2.90  sim_smt_subsumption:                    0
% 19.79/2.90  
%------------------------------------------------------------------------------
