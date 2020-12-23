%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:49 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  216 (5839 expanded)
%              Number of clauses        :  139 (1914 expanded)
%              Number of leaves         :   20 (1095 expanded)
%              Depth                    :   27
%              Number of atoms          :  662 (32489 expanded)
%              Number of equality atoms :  331 (8793 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f54,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f54])).

fof(f93,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f101,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2087,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_751,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_753,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_37])).

cnf(c_2086,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2092,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3916,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2086,c_2092])).

cnf(c_4041,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_753,c_3916])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2095,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5400,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_2095])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_5868,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5400,c_42,c_2393])).

cnf(c_5869,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5868])).

cnf(c_5880,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2087,c_5869])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2088,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6028,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5880,c_2088])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2089,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6125,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_2089])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2478,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2576,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2478])).

cnf(c_6299,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6125,c_39,c_37,c_2576])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5569,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_2090])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2568,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_2569,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2568])).

cnf(c_5704,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5569,c_40,c_42,c_2569])).

cnf(c_6308,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6299,c_5704])).

cnf(c_6778,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6028,c_6308])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_761,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_762,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_447,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_19])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_774,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_762,c_19,c_448])).

cnf(c_2074,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_6306,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6299,c_2074])).

cnf(c_6322,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6306,c_6308])).

cnf(c_9338,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5880,c_6322])).

cnf(c_9429,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6778,c_9338])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2091,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6997,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6299,c_2091])).

cnf(c_7586,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6997,c_40,c_42])).

cnf(c_2093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7598,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7586,c_2093])).

cnf(c_2083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_7597,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7586,c_2083])).

cnf(c_10877,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9429,c_7598,c_7597])).

cnf(c_7595,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_7586,c_2092])).

cnf(c_10894,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_10877,c_7595])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_10920,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10877,c_35])).

cnf(c_10921,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10920])).

cnf(c_11016,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10894,c_10921])).

cnf(c_10899,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10877,c_7586])).

cnf(c_10997,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10899,c_10921])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_10999,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10997,c_6])).

cnf(c_22,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_578,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_579,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_593,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_579,c_8])).

cnf(c_2082,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_599,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_2636,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_2637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2636])).

cnf(c_2642,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_40,c_42,c_599,c_2637])).

cnf(c_2643,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2642])).

cnf(c_6304,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6299,c_2643])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_105,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_113,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2421,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1381,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2604,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_2606,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_1380,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2437,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_2706,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_1379,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2707,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2590,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2920,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_3355,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_3356,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3355])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4222,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6572,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6304,c_36,c_35,c_105,c_111,c_113,c_114,c_2421,c_2606,c_2706,c_2707,c_2920,c_3356,c_4222,c_5880,c_6322])).

cnf(c_10902,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10877,c_6572])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_10983,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10902,c_5])).

cnf(c_11001,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10999,c_10983])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_676,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_2078,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_2295,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2078,c_6])).

cnf(c_2712,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_40,c_42,c_2637])).

cnf(c_2713,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2712])).

cnf(c_6303,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6299,c_2713])).

cnf(c_6581,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6303,c_6572])).

cnf(c_10901,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10877,c_6581])).

cnf(c_10989,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10901,c_5])).

cnf(c_11002,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10999,c_10989])).

cnf(c_11006,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11001,c_11002])).

cnf(c_11018,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11016,c_11006])).

cnf(c_2100,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5878,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2100,c_5869])).

cnf(c_2489,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2491,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2489])).

cnf(c_2761,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10736,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5878,c_37,c_2392,c_2491,c_2761])).

cnf(c_11021,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11018,c_10736])).

cnf(c_11022,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11021])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.77/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.01  
% 3.77/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.01  
% 3.77/1.01  ------  iProver source info
% 3.77/1.01  
% 3.77/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.01  git: non_committed_changes: false
% 3.77/1.01  git: last_make_outside_of_git: false
% 3.77/1.01  
% 3.77/1.01  ------ 
% 3.77/1.01  
% 3.77/1.01  ------ Input Options
% 3.77/1.01  
% 3.77/1.01  --out_options                           all
% 3.77/1.01  --tptp_safe_out                         true
% 3.77/1.01  --problem_path                          ""
% 3.77/1.01  --include_path                          ""
% 3.77/1.01  --clausifier                            res/vclausify_rel
% 3.77/1.01  --clausifier_options                    --mode clausify
% 3.77/1.01  --stdin                                 false
% 3.77/1.01  --stats_out                             all
% 3.77/1.01  
% 3.77/1.01  ------ General Options
% 3.77/1.01  
% 3.77/1.01  --fof                                   false
% 3.77/1.01  --time_out_real                         305.
% 3.77/1.01  --time_out_virtual                      -1.
% 3.77/1.01  --symbol_type_check                     false
% 3.77/1.01  --clausify_out                          false
% 3.77/1.01  --sig_cnt_out                           false
% 3.77/1.01  --trig_cnt_out                          false
% 3.77/1.01  --trig_cnt_out_tolerance                1.
% 3.77/1.01  --trig_cnt_out_sk_spl                   false
% 3.77/1.01  --abstr_cl_out                          false
% 3.77/1.01  
% 3.77/1.01  ------ Global Options
% 3.77/1.01  
% 3.77/1.01  --schedule                              default
% 3.77/1.01  --add_important_lit                     false
% 3.77/1.01  --prop_solver_per_cl                    1000
% 3.77/1.01  --min_unsat_core                        false
% 3.77/1.01  --soft_assumptions                      false
% 3.77/1.01  --soft_lemma_size                       3
% 3.77/1.01  --prop_impl_unit_size                   0
% 3.77/1.01  --prop_impl_unit                        []
% 3.77/1.01  --share_sel_clauses                     true
% 3.77/1.01  --reset_solvers                         false
% 3.77/1.01  --bc_imp_inh                            [conj_cone]
% 3.77/1.01  --conj_cone_tolerance                   3.
% 3.77/1.01  --extra_neg_conj                        none
% 3.77/1.01  --large_theory_mode                     true
% 3.77/1.01  --prolific_symb_bound                   200
% 3.77/1.01  --lt_threshold                          2000
% 3.77/1.01  --clause_weak_htbl                      true
% 3.77/1.01  --gc_record_bc_elim                     false
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing Options
% 3.77/1.01  
% 3.77/1.01  --preprocessing_flag                    true
% 3.77/1.01  --time_out_prep_mult                    0.1
% 3.77/1.01  --splitting_mode                        input
% 3.77/1.01  --splitting_grd                         true
% 3.77/1.01  --splitting_cvd                         false
% 3.77/1.01  --splitting_cvd_svl                     false
% 3.77/1.01  --splitting_nvd                         32
% 3.77/1.01  --sub_typing                            true
% 3.77/1.01  --prep_gs_sim                           true
% 3.77/1.01  --prep_unflatten                        true
% 3.77/1.01  --prep_res_sim                          true
% 3.77/1.01  --prep_upred                            true
% 3.77/1.01  --prep_sem_filter                       exhaustive
% 3.77/1.01  --prep_sem_filter_out                   false
% 3.77/1.01  --pred_elim                             true
% 3.77/1.01  --res_sim_input                         true
% 3.77/1.01  --eq_ax_congr_red                       true
% 3.77/1.01  --pure_diseq_elim                       true
% 3.77/1.01  --brand_transform                       false
% 3.77/1.01  --non_eq_to_eq                          false
% 3.77/1.01  --prep_def_merge                        true
% 3.77/1.01  --prep_def_merge_prop_impl              false
% 3.77/1.01  --prep_def_merge_mbd                    true
% 3.77/1.01  --prep_def_merge_tr_red                 false
% 3.77/1.01  --prep_def_merge_tr_cl                  false
% 3.77/1.01  --smt_preprocessing                     true
% 3.77/1.01  --smt_ac_axioms                         fast
% 3.77/1.01  --preprocessed_out                      false
% 3.77/1.01  --preprocessed_stats                    false
% 3.77/1.01  
% 3.77/1.01  ------ Abstraction refinement Options
% 3.77/1.01  
% 3.77/1.01  --abstr_ref                             []
% 3.77/1.01  --abstr_ref_prep                        false
% 3.77/1.01  --abstr_ref_until_sat                   false
% 3.77/1.01  --abstr_ref_sig_restrict                funpre
% 3.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/1.01  --abstr_ref_under                       []
% 3.77/1.01  
% 3.77/1.01  ------ SAT Options
% 3.77/1.01  
% 3.77/1.01  --sat_mode                              false
% 3.77/1.01  --sat_fm_restart_options                ""
% 3.77/1.01  --sat_gr_def                            false
% 3.77/1.01  --sat_epr_types                         true
% 3.77/1.01  --sat_non_cyclic_types                  false
% 3.77/1.01  --sat_finite_models                     false
% 3.77/1.01  --sat_fm_lemmas                         false
% 3.77/1.01  --sat_fm_prep                           false
% 3.77/1.01  --sat_fm_uc_incr                        true
% 3.77/1.01  --sat_out_model                         small
% 3.77/1.01  --sat_out_clauses                       false
% 3.77/1.01  
% 3.77/1.01  ------ QBF Options
% 3.77/1.01  
% 3.77/1.01  --qbf_mode                              false
% 3.77/1.01  --qbf_elim_univ                         false
% 3.77/1.01  --qbf_dom_inst                          none
% 3.77/1.01  --qbf_dom_pre_inst                      false
% 3.77/1.01  --qbf_sk_in                             false
% 3.77/1.01  --qbf_pred_elim                         true
% 3.77/1.01  --qbf_split                             512
% 3.77/1.01  
% 3.77/1.01  ------ BMC1 Options
% 3.77/1.01  
% 3.77/1.01  --bmc1_incremental                      false
% 3.77/1.01  --bmc1_axioms                           reachable_all
% 3.77/1.01  --bmc1_min_bound                        0
% 3.77/1.01  --bmc1_max_bound                        -1
% 3.77/1.01  --bmc1_max_bound_default                -1
% 3.77/1.01  --bmc1_symbol_reachability              true
% 3.77/1.01  --bmc1_property_lemmas                  false
% 3.77/1.01  --bmc1_k_induction                      false
% 3.77/1.01  --bmc1_non_equiv_states                 false
% 3.77/1.01  --bmc1_deadlock                         false
% 3.77/1.01  --bmc1_ucm                              false
% 3.77/1.01  --bmc1_add_unsat_core                   none
% 3.77/1.01  --bmc1_unsat_core_children              false
% 3.77/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/1.01  --bmc1_out_stat                         full
% 3.77/1.01  --bmc1_ground_init                      false
% 3.77/1.01  --bmc1_pre_inst_next_state              false
% 3.77/1.01  --bmc1_pre_inst_state                   false
% 3.77/1.01  --bmc1_pre_inst_reach_state             false
% 3.77/1.01  --bmc1_out_unsat_core                   false
% 3.77/1.01  --bmc1_aig_witness_out                  false
% 3.77/1.01  --bmc1_verbose                          false
% 3.77/1.01  --bmc1_dump_clauses_tptp                false
% 3.77/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.77/1.01  --bmc1_dump_file                        -
% 3.77/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.77/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.77/1.01  --bmc1_ucm_extend_mode                  1
% 3.77/1.01  --bmc1_ucm_init_mode                    2
% 3.77/1.01  --bmc1_ucm_cone_mode                    none
% 3.77/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.77/1.01  --bmc1_ucm_relax_model                  4
% 3.77/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.77/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/1.01  --bmc1_ucm_layered_model                none
% 3.77/1.01  --bmc1_ucm_max_lemma_size               10
% 3.77/1.01  
% 3.77/1.01  ------ AIG Options
% 3.77/1.01  
% 3.77/1.01  --aig_mode                              false
% 3.77/1.01  
% 3.77/1.01  ------ Instantiation Options
% 3.77/1.01  
% 3.77/1.01  --instantiation_flag                    true
% 3.77/1.01  --inst_sos_flag                         false
% 3.77/1.01  --inst_sos_phase                        true
% 3.77/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/1.01  --inst_lit_sel_side                     num_symb
% 3.77/1.01  --inst_solver_per_active                1400
% 3.77/1.01  --inst_solver_calls_frac                1.
% 3.77/1.01  --inst_passive_queue_type               priority_queues
% 3.77/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/1.01  --inst_passive_queues_freq              [25;2]
% 3.77/1.01  --inst_dismatching                      true
% 3.77/1.01  --inst_eager_unprocessed_to_passive     true
% 3.77/1.01  --inst_prop_sim_given                   true
% 3.77/1.01  --inst_prop_sim_new                     false
% 3.77/1.01  --inst_subs_new                         false
% 3.77/1.01  --inst_eq_res_simp                      false
% 3.77/1.01  --inst_subs_given                       false
% 3.77/1.01  --inst_orphan_elimination               true
% 3.77/1.01  --inst_learning_loop_flag               true
% 3.77/1.01  --inst_learning_start                   3000
% 3.77/1.01  --inst_learning_factor                  2
% 3.77/1.01  --inst_start_prop_sim_after_learn       3
% 3.77/1.01  --inst_sel_renew                        solver
% 3.77/1.01  --inst_lit_activity_flag                true
% 3.77/1.01  --inst_restr_to_given                   false
% 3.77/1.01  --inst_activity_threshold               500
% 3.77/1.01  --inst_out_proof                        true
% 3.77/1.01  
% 3.77/1.01  ------ Resolution Options
% 3.77/1.01  
% 3.77/1.01  --resolution_flag                       true
% 3.77/1.01  --res_lit_sel                           adaptive
% 3.77/1.01  --res_lit_sel_side                      none
% 3.77/1.01  --res_ordering                          kbo
% 3.77/1.01  --res_to_prop_solver                    active
% 3.77/1.01  --res_prop_simpl_new                    false
% 3.77/1.01  --res_prop_simpl_given                  true
% 3.77/1.01  --res_passive_queue_type                priority_queues
% 3.77/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/1.01  --res_passive_queues_freq               [15;5]
% 3.77/1.01  --res_forward_subs                      full
% 3.77/1.01  --res_backward_subs                     full
% 3.77/1.01  --res_forward_subs_resolution           true
% 3.77/1.01  --res_backward_subs_resolution          true
% 3.77/1.01  --res_orphan_elimination                true
% 3.77/1.01  --res_time_limit                        2.
% 3.77/1.01  --res_out_proof                         true
% 3.77/1.01  
% 3.77/1.01  ------ Superposition Options
% 3.77/1.01  
% 3.77/1.01  --superposition_flag                    true
% 3.77/1.01  --sup_passive_queue_type                priority_queues
% 3.77/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.77/1.01  --demod_completeness_check              fast
% 3.77/1.01  --demod_use_ground                      true
% 3.77/1.01  --sup_to_prop_solver                    passive
% 3.77/1.01  --sup_prop_simpl_new                    true
% 3.77/1.01  --sup_prop_simpl_given                  true
% 3.77/1.01  --sup_fun_splitting                     false
% 3.77/1.01  --sup_smt_interval                      50000
% 3.77/1.01  
% 3.77/1.01  ------ Superposition Simplification Setup
% 3.77/1.01  
% 3.77/1.01  --sup_indices_passive                   []
% 3.77/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_full_bw                           [BwDemod]
% 3.77/1.01  --sup_immed_triv                        [TrivRules]
% 3.77/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_immed_bw_main                     []
% 3.77/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/1.01  
% 3.77/1.01  ------ Combination Options
% 3.77/1.01  
% 3.77/1.01  --comb_res_mult                         3
% 3.77/1.01  --comb_sup_mult                         2
% 3.77/1.01  --comb_inst_mult                        10
% 3.77/1.01  
% 3.77/1.01  ------ Debug Options
% 3.77/1.01  
% 3.77/1.01  --dbg_backtrace                         false
% 3.77/1.01  --dbg_dump_prop_clauses                 false
% 3.77/1.01  --dbg_dump_prop_clauses_file            -
% 3.77/1.01  --dbg_out_stat                          false
% 3.77/1.01  ------ Parsing...
% 3.77/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.01  ------ Proving...
% 3.77/1.01  ------ Problem Properties 
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  clauses                                 38
% 3.77/1.01  conjectures                             4
% 3.77/1.01  EPR                                     8
% 3.77/1.01  Horn                                    33
% 3.77/1.01  unary                                   10
% 3.77/1.01  binary                                  9
% 3.77/1.01  lits                                    99
% 3.77/1.01  lits eq                                 36
% 3.77/1.01  fd_pure                                 0
% 3.77/1.01  fd_pseudo                               0
% 3.77/1.01  fd_cond                                 3
% 3.77/1.01  fd_pseudo_cond                          1
% 3.77/1.01  AC symbols                              0
% 3.77/1.01  
% 3.77/1.01  ------ Schedule dynamic 5 is on 
% 3.77/1.01  
% 3.77/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  ------ 
% 3.77/1.01  Current options:
% 3.77/1.01  ------ 
% 3.77/1.01  
% 3.77/1.01  ------ Input Options
% 3.77/1.01  
% 3.77/1.01  --out_options                           all
% 3.77/1.01  --tptp_safe_out                         true
% 3.77/1.01  --problem_path                          ""
% 3.77/1.01  --include_path                          ""
% 3.77/1.01  --clausifier                            res/vclausify_rel
% 3.77/1.01  --clausifier_options                    --mode clausify
% 3.77/1.01  --stdin                                 false
% 3.77/1.01  --stats_out                             all
% 3.77/1.01  
% 3.77/1.01  ------ General Options
% 3.77/1.01  
% 3.77/1.01  --fof                                   false
% 3.77/1.01  --time_out_real                         305.
% 3.77/1.01  --time_out_virtual                      -1.
% 3.77/1.01  --symbol_type_check                     false
% 3.77/1.01  --clausify_out                          false
% 3.77/1.01  --sig_cnt_out                           false
% 3.77/1.01  --trig_cnt_out                          false
% 3.77/1.01  --trig_cnt_out_tolerance                1.
% 3.77/1.01  --trig_cnt_out_sk_spl                   false
% 3.77/1.01  --abstr_cl_out                          false
% 3.77/1.01  
% 3.77/1.01  ------ Global Options
% 3.77/1.01  
% 3.77/1.01  --schedule                              default
% 3.77/1.01  --add_important_lit                     false
% 3.77/1.01  --prop_solver_per_cl                    1000
% 3.77/1.01  --min_unsat_core                        false
% 3.77/1.01  --soft_assumptions                      false
% 3.77/1.01  --soft_lemma_size                       3
% 3.77/1.01  --prop_impl_unit_size                   0
% 3.77/1.01  --prop_impl_unit                        []
% 3.77/1.01  --share_sel_clauses                     true
% 3.77/1.01  --reset_solvers                         false
% 3.77/1.01  --bc_imp_inh                            [conj_cone]
% 3.77/1.01  --conj_cone_tolerance                   3.
% 3.77/1.01  --extra_neg_conj                        none
% 3.77/1.01  --large_theory_mode                     true
% 3.77/1.01  --prolific_symb_bound                   200
% 3.77/1.01  --lt_threshold                          2000
% 3.77/1.01  --clause_weak_htbl                      true
% 3.77/1.01  --gc_record_bc_elim                     false
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing Options
% 3.77/1.01  
% 3.77/1.01  --preprocessing_flag                    true
% 3.77/1.01  --time_out_prep_mult                    0.1
% 3.77/1.01  --splitting_mode                        input
% 3.77/1.01  --splitting_grd                         true
% 3.77/1.01  --splitting_cvd                         false
% 3.77/1.01  --splitting_cvd_svl                     false
% 3.77/1.01  --splitting_nvd                         32
% 3.77/1.01  --sub_typing                            true
% 3.77/1.01  --prep_gs_sim                           true
% 3.77/1.01  --prep_unflatten                        true
% 3.77/1.01  --prep_res_sim                          true
% 3.77/1.01  --prep_upred                            true
% 3.77/1.01  --prep_sem_filter                       exhaustive
% 3.77/1.01  --prep_sem_filter_out                   false
% 3.77/1.01  --pred_elim                             true
% 3.77/1.01  --res_sim_input                         true
% 3.77/1.01  --eq_ax_congr_red                       true
% 3.77/1.01  --pure_diseq_elim                       true
% 3.77/1.01  --brand_transform                       false
% 3.77/1.01  --non_eq_to_eq                          false
% 3.77/1.01  --prep_def_merge                        true
% 3.77/1.01  --prep_def_merge_prop_impl              false
% 3.77/1.01  --prep_def_merge_mbd                    true
% 3.77/1.01  --prep_def_merge_tr_red                 false
% 3.77/1.01  --prep_def_merge_tr_cl                  false
% 3.77/1.01  --smt_preprocessing                     true
% 3.77/1.01  --smt_ac_axioms                         fast
% 3.77/1.01  --preprocessed_out                      false
% 3.77/1.01  --preprocessed_stats                    false
% 3.77/1.01  
% 3.77/1.01  ------ Abstraction refinement Options
% 3.77/1.01  
% 3.77/1.01  --abstr_ref                             []
% 3.77/1.01  --abstr_ref_prep                        false
% 3.77/1.01  --abstr_ref_until_sat                   false
% 3.77/1.01  --abstr_ref_sig_restrict                funpre
% 3.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/1.01  --abstr_ref_under                       []
% 3.77/1.01  
% 3.77/1.01  ------ SAT Options
% 3.77/1.01  
% 3.77/1.01  --sat_mode                              false
% 3.77/1.01  --sat_fm_restart_options                ""
% 3.77/1.01  --sat_gr_def                            false
% 3.77/1.01  --sat_epr_types                         true
% 3.77/1.01  --sat_non_cyclic_types                  false
% 3.77/1.01  --sat_finite_models                     false
% 3.77/1.01  --sat_fm_lemmas                         false
% 3.77/1.01  --sat_fm_prep                           false
% 3.77/1.01  --sat_fm_uc_incr                        true
% 3.77/1.01  --sat_out_model                         small
% 3.77/1.01  --sat_out_clauses                       false
% 3.77/1.01  
% 3.77/1.01  ------ QBF Options
% 3.77/1.01  
% 3.77/1.01  --qbf_mode                              false
% 3.77/1.01  --qbf_elim_univ                         false
% 3.77/1.01  --qbf_dom_inst                          none
% 3.77/1.01  --qbf_dom_pre_inst                      false
% 3.77/1.01  --qbf_sk_in                             false
% 3.77/1.01  --qbf_pred_elim                         true
% 3.77/1.01  --qbf_split                             512
% 3.77/1.01  
% 3.77/1.01  ------ BMC1 Options
% 3.77/1.01  
% 3.77/1.01  --bmc1_incremental                      false
% 3.77/1.01  --bmc1_axioms                           reachable_all
% 3.77/1.01  --bmc1_min_bound                        0
% 3.77/1.01  --bmc1_max_bound                        -1
% 3.77/1.01  --bmc1_max_bound_default                -1
% 3.77/1.01  --bmc1_symbol_reachability              true
% 3.77/1.01  --bmc1_property_lemmas                  false
% 3.77/1.01  --bmc1_k_induction                      false
% 3.77/1.01  --bmc1_non_equiv_states                 false
% 3.77/1.01  --bmc1_deadlock                         false
% 3.77/1.01  --bmc1_ucm                              false
% 3.77/1.01  --bmc1_add_unsat_core                   none
% 3.77/1.01  --bmc1_unsat_core_children              false
% 3.77/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/1.01  --bmc1_out_stat                         full
% 3.77/1.01  --bmc1_ground_init                      false
% 3.77/1.01  --bmc1_pre_inst_next_state              false
% 3.77/1.01  --bmc1_pre_inst_state                   false
% 3.77/1.01  --bmc1_pre_inst_reach_state             false
% 3.77/1.01  --bmc1_out_unsat_core                   false
% 3.77/1.01  --bmc1_aig_witness_out                  false
% 3.77/1.01  --bmc1_verbose                          false
% 3.77/1.01  --bmc1_dump_clauses_tptp                false
% 3.77/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.77/1.01  --bmc1_dump_file                        -
% 3.77/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.77/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.77/1.01  --bmc1_ucm_extend_mode                  1
% 3.77/1.01  --bmc1_ucm_init_mode                    2
% 3.77/1.01  --bmc1_ucm_cone_mode                    none
% 3.77/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.77/1.01  --bmc1_ucm_relax_model                  4
% 3.77/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.77/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/1.01  --bmc1_ucm_layered_model                none
% 3.77/1.01  --bmc1_ucm_max_lemma_size               10
% 3.77/1.01  
% 3.77/1.01  ------ AIG Options
% 3.77/1.01  
% 3.77/1.01  --aig_mode                              false
% 3.77/1.01  
% 3.77/1.01  ------ Instantiation Options
% 3.77/1.01  
% 3.77/1.01  --instantiation_flag                    true
% 3.77/1.01  --inst_sos_flag                         false
% 3.77/1.01  --inst_sos_phase                        true
% 3.77/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/1.01  --inst_lit_sel_side                     none
% 3.77/1.01  --inst_solver_per_active                1400
% 3.77/1.01  --inst_solver_calls_frac                1.
% 3.77/1.01  --inst_passive_queue_type               priority_queues
% 3.77/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/1.01  --inst_passive_queues_freq              [25;2]
% 3.77/1.01  --inst_dismatching                      true
% 3.77/1.01  --inst_eager_unprocessed_to_passive     true
% 3.77/1.01  --inst_prop_sim_given                   true
% 3.77/1.01  --inst_prop_sim_new                     false
% 3.77/1.01  --inst_subs_new                         false
% 3.77/1.01  --inst_eq_res_simp                      false
% 3.77/1.01  --inst_subs_given                       false
% 3.77/1.01  --inst_orphan_elimination               true
% 3.77/1.01  --inst_learning_loop_flag               true
% 3.77/1.01  --inst_learning_start                   3000
% 3.77/1.01  --inst_learning_factor                  2
% 3.77/1.01  --inst_start_prop_sim_after_learn       3
% 3.77/1.01  --inst_sel_renew                        solver
% 3.77/1.01  --inst_lit_activity_flag                true
% 3.77/1.01  --inst_restr_to_given                   false
% 3.77/1.01  --inst_activity_threshold               500
% 3.77/1.01  --inst_out_proof                        true
% 3.77/1.01  
% 3.77/1.01  ------ Resolution Options
% 3.77/1.01  
% 3.77/1.01  --resolution_flag                       false
% 3.77/1.01  --res_lit_sel                           adaptive
% 3.77/1.01  --res_lit_sel_side                      none
% 3.77/1.01  --res_ordering                          kbo
% 3.77/1.01  --res_to_prop_solver                    active
% 3.77/1.01  --res_prop_simpl_new                    false
% 3.77/1.01  --res_prop_simpl_given                  true
% 3.77/1.01  --res_passive_queue_type                priority_queues
% 3.77/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/1.01  --res_passive_queues_freq               [15;5]
% 3.77/1.01  --res_forward_subs                      full
% 3.77/1.01  --res_backward_subs                     full
% 3.77/1.01  --res_forward_subs_resolution           true
% 3.77/1.01  --res_backward_subs_resolution          true
% 3.77/1.01  --res_orphan_elimination                true
% 3.77/1.01  --res_time_limit                        2.
% 3.77/1.01  --res_out_proof                         true
% 3.77/1.01  
% 3.77/1.01  ------ Superposition Options
% 3.77/1.01  
% 3.77/1.01  --superposition_flag                    true
% 3.77/1.01  --sup_passive_queue_type                priority_queues
% 3.77/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.77/1.01  --demod_completeness_check              fast
% 3.77/1.01  --demod_use_ground                      true
% 3.77/1.01  --sup_to_prop_solver                    passive
% 3.77/1.01  --sup_prop_simpl_new                    true
% 3.77/1.01  --sup_prop_simpl_given                  true
% 3.77/1.01  --sup_fun_splitting                     false
% 3.77/1.01  --sup_smt_interval                      50000
% 3.77/1.01  
% 3.77/1.01  ------ Superposition Simplification Setup
% 3.77/1.01  
% 3.77/1.01  --sup_indices_passive                   []
% 3.77/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_full_bw                           [BwDemod]
% 3.77/1.01  --sup_immed_triv                        [TrivRules]
% 3.77/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_immed_bw_main                     []
% 3.77/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/1.01  
% 3.77/1.01  ------ Combination Options
% 3.77/1.01  
% 3.77/1.01  --comb_res_mult                         3
% 3.77/1.01  --comb_sup_mult                         2
% 3.77/1.01  --comb_inst_mult                        10
% 3.77/1.01  
% 3.77/1.01  ------ Debug Options
% 3.77/1.01  
% 3.77/1.01  --dbg_backtrace                         false
% 3.77/1.01  --dbg_dump_prop_clauses                 false
% 3.77/1.01  --dbg_dump_prop_clauses_file            -
% 3.77/1.01  --dbg_out_stat                          false
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  ------ Proving...
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  % SZS status Theorem for theBenchmark.p
% 3.77/1.01  
% 3.77/1.01   Resolution empty clause
% 3.77/1.01  
% 3.77/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.01  
% 3.77/1.01  fof(f21,conjecture,(
% 3.77/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f22,negated_conjecture,(
% 3.77/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.77/1.01    inference(negated_conjecture,[],[f21])).
% 3.77/1.01  
% 3.77/1.01  fof(f45,plain,(
% 3.77/1.01    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.77/1.01    inference(ennf_transformation,[],[f22])).
% 3.77/1.01  
% 3.77/1.01  fof(f46,plain,(
% 3.77/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.77/1.01    inference(flattening,[],[f45])).
% 3.77/1.01  
% 3.77/1.01  fof(f54,plain,(
% 3.77/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.77/1.01    introduced(choice_axiom,[])).
% 3.77/1.01  
% 3.77/1.01  fof(f55,plain,(
% 3.77/1.01    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.77/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f54])).
% 3.77/1.01  
% 3.77/1.01  fof(f93,plain,(
% 3.77/1.01    r1_tarski(sK2,sK0)),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f17,axiom,(
% 3.77/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f37,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(ennf_transformation,[],[f17])).
% 3.77/1.01  
% 3.77/1.01  fof(f38,plain,(
% 3.77/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(flattening,[],[f37])).
% 3.77/1.01  
% 3.77/1.01  fof(f53,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(nnf_transformation,[],[f38])).
% 3.77/1.01  
% 3.77/1.01  fof(f78,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f53])).
% 3.77/1.01  
% 3.77/1.01  fof(f91,plain,(
% 3.77/1.01    v1_funct_2(sK3,sK0,sK1)),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f92,plain,(
% 3.77/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f16,axiom,(
% 3.77/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f36,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(ennf_transformation,[],[f16])).
% 3.77/1.01  
% 3.77/1.01  fof(f77,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f36])).
% 3.77/1.01  
% 3.77/1.01  fof(f11,axiom,(
% 3.77/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f29,plain,(
% 3.77/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.77/1.01    inference(ennf_transformation,[],[f11])).
% 3.77/1.01  
% 3.77/1.01  fof(f30,plain,(
% 3.77/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.77/1.01    inference(flattening,[],[f29])).
% 3.77/1.01  
% 3.77/1.01  fof(f72,plain,(
% 3.77/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f30])).
% 3.77/1.01  
% 3.77/1.01  fof(f14,axiom,(
% 3.77/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f34,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(ennf_transformation,[],[f14])).
% 3.77/1.01  
% 3.77/1.01  fof(f75,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f34])).
% 3.77/1.01  
% 3.77/1.01  fof(f20,axiom,(
% 3.77/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f43,plain,(
% 3.77/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.77/1.01    inference(ennf_transformation,[],[f20])).
% 3.77/1.01  
% 3.77/1.01  fof(f44,plain,(
% 3.77/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.77/1.01    inference(flattening,[],[f43])).
% 3.77/1.01  
% 3.77/1.01  fof(f89,plain,(
% 3.77/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f44])).
% 3.77/1.01  
% 3.77/1.01  fof(f19,axiom,(
% 3.77/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f41,plain,(
% 3.77/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.77/1.01    inference(ennf_transformation,[],[f19])).
% 3.77/1.01  
% 3.77/1.01  fof(f42,plain,(
% 3.77/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.77/1.01    inference(flattening,[],[f41])).
% 3.77/1.01  
% 3.77/1.01  fof(f86,plain,(
% 3.77/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f42])).
% 3.77/1.01  
% 3.77/1.01  fof(f90,plain,(
% 3.77/1.01    v1_funct_1(sK3)),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f18,axiom,(
% 3.77/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f39,plain,(
% 3.77/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.77/1.01    inference(ennf_transformation,[],[f18])).
% 3.77/1.01  
% 3.77/1.01  fof(f40,plain,(
% 3.77/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.77/1.01    inference(flattening,[],[f39])).
% 3.77/1.01  
% 3.77/1.01  fof(f84,plain,(
% 3.77/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f40])).
% 3.77/1.01  
% 3.77/1.01  fof(f88,plain,(
% 3.77/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f44])).
% 3.77/1.01  
% 3.77/1.01  fof(f95,plain,(
% 3.77/1.01    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f15,axiom,(
% 3.77/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f23,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.77/1.01    inference(pure_predicate_removal,[],[f15])).
% 3.77/1.01  
% 3.77/1.01  fof(f35,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.01    inference(ennf_transformation,[],[f23])).
% 3.77/1.01  
% 3.77/1.01  fof(f76,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f35])).
% 3.77/1.01  
% 3.77/1.01  fof(f8,axiom,(
% 3.77/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f27,plain,(
% 3.77/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/1.01    inference(ennf_transformation,[],[f8])).
% 3.77/1.01  
% 3.77/1.01  fof(f52,plain,(
% 3.77/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/1.01    inference(nnf_transformation,[],[f27])).
% 3.77/1.01  
% 3.77/1.01  fof(f67,plain,(
% 3.77/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f52])).
% 3.77/1.01  
% 3.77/1.01  fof(f85,plain,(
% 3.77/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f40])).
% 3.77/1.01  
% 3.77/1.01  fof(f94,plain,(
% 3.77/1.01    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.77/1.01    inference(cnf_transformation,[],[f55])).
% 3.77/1.01  
% 3.77/1.01  fof(f4,axiom,(
% 3.77/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f49,plain,(
% 3.77/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.77/1.01    inference(nnf_transformation,[],[f4])).
% 3.77/1.01  
% 3.77/1.01  fof(f50,plain,(
% 3.77/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.77/1.01    inference(flattening,[],[f49])).
% 3.77/1.01  
% 3.77/1.01  fof(f62,plain,(
% 3.77/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.77/1.01    inference(cnf_transformation,[],[f50])).
% 3.77/1.01  
% 3.77/1.01  fof(f99,plain,(
% 3.77/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.77/1.01    inference(equality_resolution,[],[f62])).
% 3.77/1.01  
% 3.77/1.01  fof(f83,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f53])).
% 3.77/1.01  
% 3.77/1.01  fof(f100,plain,(
% 3.77/1.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(equality_resolution,[],[f83])).
% 3.77/1.01  
% 3.77/1.01  fof(f101,plain,(
% 3.77/1.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.77/1.01    inference(equality_resolution,[],[f100])).
% 3.77/1.01  
% 3.77/1.01  fof(f5,axiom,(
% 3.77/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f64,plain,(
% 3.77/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f5])).
% 3.77/1.01  
% 3.77/1.01  fof(f6,axiom,(
% 3.77/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f51,plain,(
% 3.77/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/1.01    inference(nnf_transformation,[],[f6])).
% 3.77/1.01  
% 3.77/1.01  fof(f65,plain,(
% 3.77/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f51])).
% 3.77/1.01  
% 3.77/1.01  fof(f61,plain,(
% 3.77/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f50])).
% 3.77/1.01  
% 3.77/1.01  fof(f1,axiom,(
% 3.77/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f47,plain,(
% 3.77/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.01    inference(nnf_transformation,[],[f1])).
% 3.77/1.01  
% 3.77/1.01  fof(f48,plain,(
% 3.77/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.01    inference(flattening,[],[f47])).
% 3.77/1.01  
% 3.77/1.01  fof(f58,plain,(
% 3.77/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f48])).
% 3.77/1.01  
% 3.77/1.01  fof(f2,axiom,(
% 3.77/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f25,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.77/1.01    inference(ennf_transformation,[],[f2])).
% 3.77/1.01  
% 3.77/1.01  fof(f26,plain,(
% 3.77/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.77/1.01    inference(flattening,[],[f25])).
% 3.77/1.01  
% 3.77/1.01  fof(f59,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f26])).
% 3.77/1.01  
% 3.77/1.01  fof(f3,axiom,(
% 3.77/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.77/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.01  
% 3.77/1.01  fof(f60,plain,(
% 3.77/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.77/1.01    inference(cnf_transformation,[],[f3])).
% 3.77/1.01  
% 3.77/1.01  fof(f63,plain,(
% 3.77/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.77/1.01    inference(cnf_transformation,[],[f50])).
% 3.77/1.01  
% 3.77/1.01  fof(f98,plain,(
% 3.77/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.77/1.01    inference(equality_resolution,[],[f63])).
% 3.77/1.01  
% 3.77/1.01  fof(f81,plain,(
% 3.77/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.01    inference(cnf_transformation,[],[f53])).
% 3.77/1.01  
% 3.77/1.01  fof(f103,plain,(
% 3.77/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.77/1.01    inference(equality_resolution,[],[f81])).
% 3.77/1.01  
% 3.77/1.01  cnf(c_36,negated_conjecture,
% 3.77/1.01      ( r1_tarski(sK2,sK0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2087,plain,
% 3.77/1.01      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_27,plain,
% 3.77/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.77/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.77/1.01      | k1_xboole_0 = X2 ),
% 3.77/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_38,negated_conjecture,
% 3.77/1.01      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.77/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_750,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.77/1.01      | sK3 != X0
% 3.77/1.01      | sK1 != X2
% 3.77/1.01      | sK0 != X1
% 3.77/1.01      | k1_xboole_0 = X2 ),
% 3.77/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_751,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.01      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.77/1.01      | k1_xboole_0 = sK1 ),
% 3.77/1.01      inference(unflattening,[status(thm)],[c_750]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_37,negated_conjecture,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.77/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_753,plain,
% 3.77/1.01      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.77/1.01      inference(global_propositional_subsumption,[status(thm)],[c_751,c_37]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2086,plain,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_21,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2092,plain,
% 3.77/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.77/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_3916,plain,
% 3.77/1.01      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_2086,c_2092]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_4041,plain,
% 3.77/1.01      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_753,c_3916]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_16,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.77/1.01      | ~ v1_relat_1(X1)
% 3.77/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2095,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.77/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.77/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5400,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.77/1.01      | sK1 = k1_xboole_0
% 3.77/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.77/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_4041,c_2095]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_42,plain,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_19,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2392,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.01      | v1_relat_1(sK3) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2393,plain,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5868,plain,
% 3.77/1.01      ( r1_tarski(X0,sK0) != iProver_top
% 3.77/1.01      | sK1 = k1_xboole_0
% 3.77/1.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_5400,c_42,c_2393]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5869,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.77/1.01      | sK1 = k1_xboole_0
% 3.77/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.77/1.01      inference(renaming,[status(thm)],[c_5868]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5880,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_2087,c_5869]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_31,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.77/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.01      | ~ v1_funct_1(X0)
% 3.77/1.01      | ~ v1_relat_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2088,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.77/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.77/1.01      | v1_funct_1(X0) != iProver_top
% 3.77/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6028,plain,
% 3.77/1.01      ( sK1 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.77/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.77/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.77/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_5880,c_2088]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_30,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | ~ v1_funct_1(X0)
% 3.77/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.77/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2089,plain,
% 3.77/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.77/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6125,plain,
% 3.77/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.77/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_2086,c_2089]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_39,negated_conjecture,
% 3.77/1.01      ( v1_funct_1(sK3) ),
% 3.77/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2478,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/1.01      | ~ v1_funct_1(sK3)
% 3.77/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2576,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.01      | ~ v1_funct_1(sK3)
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2478]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6299,plain,
% 3.77/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_6125,c_39,c_37,c_2576]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_29,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | ~ v1_funct_1(X0)
% 3.77/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.77/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2090,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.01      | v1_funct_1(X0) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5569,plain,
% 3.77/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.77/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_2086,c_2090]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_40,plain,
% 3.77/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2459,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/1.01      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.77/1.01      | ~ v1_funct_1(sK3) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2568,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.77/1.01      | ~ v1_funct_1(sK3) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2459]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2569,plain,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.77/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_2568]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5704,plain,
% 3.77/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_5569,c_40,c_42,c_2569]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6308,plain,
% 3.77/1.01      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_6299,c_5704]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6778,plain,
% 3.77/1.01      ( sK1 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.77/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.77/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6028,c_6308]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_32,plain,
% 3.77/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.77/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.01      | ~ v1_funct_1(X0)
% 3.77/1.01      | ~ v1_relat_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_34,negated_conjecture,
% 3.77/1.01      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.77/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.77/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_761,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.01      | ~ v1_funct_1(X0)
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | ~ v1_relat_1(X0)
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.77/1.01      | k1_relat_1(X0) != sK2
% 3.77/1.01      | sK1 != X1 ),
% 3.77/1.01      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_762,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.77/1.01      inference(unflattening,[status(thm)],[c_761]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_20,plain,
% 3.77/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.77/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_12,plain,
% 3.77/1.01      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_443,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.77/1.01      | ~ v1_relat_1(X0) ),
% 3.77/1.01      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_447,plain,
% 3.77/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 3.77/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.77/1.01      inference(global_propositional_subsumption,[status(thm)],[c_443,c_19]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_448,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.77/1.01      inference(renaming,[status(thm)],[c_447]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_774,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.77/1.01      inference(forward_subsumption_resolution,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_762,c_19,c_448]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2074,plain,
% 3.77/1.01      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6306,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_6299,c_2074]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6322,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.77/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6306,c_6308]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_9338,plain,
% 3.77/1.01      ( sK1 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_5880,c_6322]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_9429,plain,
% 3.77/1.01      ( sK1 = k1_xboole_0
% 3.77/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.77/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_6778,c_9338]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_28,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.01      | ~ v1_funct_1(X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2091,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.77/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6997,plain,
% 3.77/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.77/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_6299,c_2091]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_7586,plain,
% 3.77/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_6997,c_40,c_42]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2093,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_7598,plain,
% 3.77/1.01      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_7586,c_2093]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2083,plain,
% 3.77/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_7597,plain,
% 3.77/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_7586,c_2083]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10877,plain,
% 3.77/1.01      ( sK1 = k1_xboole_0 ),
% 3.77/1.01      inference(forward_subsumption_resolution,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_9429,c_7598,c_7597]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_7595,plain,
% 3.77/1.01      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_7586,c_2092]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10894,plain,
% 3.77/1.01      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10877,c_7595]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_35,negated_conjecture,
% 3.77/1.01      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10920,plain,
% 3.77/1.01      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10877,c_35]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10921,plain,
% 3.77/1.01      ( sK0 = k1_xboole_0 ),
% 3.77/1.01      inference(equality_resolution_simp,[status(thm)],[c_10920]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11016,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.77/1.01      inference(light_normalisation,[status(thm)],[c_10894,c_10921]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10899,plain,
% 3.77/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10877,c_7586]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10997,plain,
% 3.77/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.77/1.01      inference(light_normalisation,[status(thm)],[c_10899,c_10921]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6,plain,
% 3.77/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10999,plain,
% 3.77/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10997,c_6]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_22,plain,
% 3.77/1.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.77/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.77/1.01      | k1_xboole_0 = X0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_578,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK2 != X0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = X0 ),
% 3.77/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_579,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = sK2 ),
% 3.77/1.01      inference(unflattening,[status(thm)],[c_578]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_8,plain,
% 3.77/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.77/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_593,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = sK2 ),
% 3.77/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_579,c_8]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2082,plain,
% 3.77/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = sK2
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_599,plain,
% 3.77/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = sK2
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2636,plain,
% 3.77/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | ~ v1_funct_1(sK3) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2568]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2637,plain,
% 3.77/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.77/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_2636]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2642,plain,
% 3.77/1.01      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | k1_xboole_0 = sK2
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_2082,c_40,c_42,c_599,c_2637]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2643,plain,
% 3.77/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = sK2
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.77/1.01      inference(renaming,[status(thm)],[c_2642]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6304,plain,
% 3.77/1.01      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.77/1.01      | sK2 = k1_xboole_0
% 3.77/1.01      | sK1 != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_6299,c_2643]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_105,plain,
% 3.77/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.77/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_111,plain,
% 3.77/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_7,plain,
% 3.77/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = X1
% 3.77/1.01      | k1_xboole_0 = X0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_113,plain,
% 3.77/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_114,plain,
% 3.77/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_0,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.77/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2421,plain,
% 3.77/1.01      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.77/1.01      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.77/1.01      | sK2 = k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_1381,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.77/1.01      theory(equality) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2604,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,X1)
% 3.77/1.01      | r1_tarski(sK0,k1_xboole_0)
% 3.77/1.01      | sK0 != X0
% 3.77/1.01      | k1_xboole_0 != X1 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_1381]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2606,plain,
% 3.77/1.01      ( r1_tarski(sK0,k1_xboole_0)
% 3.77/1.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.77/1.01      | sK0 != k1_xboole_0
% 3.77/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2604]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_1380,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2437,plain,
% 3.77/1.01      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_1380]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2706,plain,
% 3.77/1.01      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2437]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_1379,plain,( X0 = X0 ),theory(equality) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2707,plain,
% 3.77/1.01      ( sK0 = sK0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_1379]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_3,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.77/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2590,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.77/1.01      | ~ r1_tarski(sK2,X0)
% 3.77/1.01      | r1_tarski(sK2,k1_xboole_0) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2920,plain,
% 3.77/1.01      ( ~ r1_tarski(sK2,sK0)
% 3.77/1.01      | r1_tarski(sK2,k1_xboole_0)
% 3.77/1.01      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2590]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_3355,plain,
% 3.77/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_1380]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_3356,plain,
% 3.77/1.01      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_3355]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_4,plain,
% 3.77/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.77/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_4222,plain,
% 3.77/1.01      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6572,plain,
% 3.77/1.01      ( sK2 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_6304,c_36,c_35,c_105,c_111,c_113,c_114,c_2421,c_2606,
% 3.77/1.01                 c_2706,c_2707,c_2920,c_3356,c_4222,c_5880,c_6322]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10902,plain,
% 3.77/1.01      ( sK2 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10877,c_6572]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5,plain,
% 3.77/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10983,plain,
% 3.77/1.01      ( sK2 = k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10902,c_5]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11001,plain,
% 3.77/1.01      ( sK2 = k1_xboole_0 ),
% 3.77/1.01      inference(backward_subsumption_resolution,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_10999,c_10983]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_24,plain,
% 3.77/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.77/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.77/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.77/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_675,plain,
% 3.77/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.77/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.77/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | sK1 != X1 ),
% 3.77/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_676,plain,
% 3.77/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.77/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.77/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.77/1.01      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0 ),
% 3.77/1.01      inference(unflattening,[status(thm)],[c_675]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2078,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2295,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.77/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_2078,c_6]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2712,plain,
% 3.77/1.01      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_2295,c_40,c_42,c_2637]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2713,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(renaming,[status(thm)],[c_2712]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6303,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | sK2 != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_6299,c_2713]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_6581,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(global_propositional_subsumption,[status(thm)],[c_6303,c_6572]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10901,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10877,c_6581]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10989,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.77/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_10901,c_5]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11002,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.77/1.01      inference(backward_subsumption_resolution,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_10999,c_10989]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11006,plain,
% 3.77/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_11001,c_11002]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11018,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.77/1.01      inference(demodulation,[status(thm)],[c_11016,c_11006]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2100,plain,
% 3.77/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.77/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_5878,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.77/1.01      | sK1 = k1_xboole_0 ),
% 3.77/1.01      inference(superposition,[status(thm)],[c_2100,c_5869]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2489,plain,
% 3.77/1.01      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.77/1.01      | ~ v1_relat_1(sK3)
% 3.77/1.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2491,plain,
% 3.77/1.01      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.77/1.01      | ~ v1_relat_1(sK3)
% 3.77/1.01      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_2489]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_2761,plain,
% 3.77/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.77/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_10736,plain,
% 3.77/1.01      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.77/1.01      inference(global_propositional_subsumption,
% 3.77/1.01                [status(thm)],
% 3.77/1.01                [c_5878,c_37,c_2392,c_2491,c_2761]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11021,plain,
% 3.77/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.77/1.01      inference(light_normalisation,[status(thm)],[c_11018,c_10736]) ).
% 3.77/1.01  
% 3.77/1.01  cnf(c_11022,plain,
% 3.77/1.01      ( $false ),
% 3.77/1.01      inference(equality_resolution_simp,[status(thm)],[c_11021]) ).
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.01  
% 3.77/1.01  ------                               Statistics
% 3.77/1.01  
% 3.77/1.01  ------ General
% 3.77/1.01  
% 3.77/1.01  abstr_ref_over_cycles:                  0
% 3.77/1.01  abstr_ref_under_cycles:                 0
% 3.77/1.01  gc_basic_clause_elim:                   0
% 3.77/1.01  forced_gc_time:                         0
% 3.77/1.01  parsing_time:                           0.01
% 3.77/1.01  unif_index_cands_time:                  0.
% 3.77/1.01  unif_index_add_time:                    0.
% 3.77/1.01  orderings_time:                         0.
% 3.77/1.01  out_proof_time:                         0.017
% 3.77/1.01  total_time:                             0.283
% 3.77/1.01  num_of_symbols:                         49
% 3.77/1.01  num_of_terms:                           7235
% 3.77/1.01  
% 3.77/1.01  ------ Preprocessing
% 3.77/1.01  
% 3.77/1.01  num_of_splits:                          0
% 3.77/1.01  num_of_split_atoms:                     0
% 3.77/1.01  num_of_reused_defs:                     0
% 3.77/1.01  num_eq_ax_congr_red:                    13
% 3.77/1.01  num_of_sem_filtered_clauses:            1
% 3.77/1.01  num_of_subtypes:                        0
% 3.77/1.01  monotx_restored_types:                  0
% 3.77/1.01  sat_num_of_epr_types:                   0
% 3.77/1.01  sat_num_of_non_cyclic_types:            0
% 3.77/1.01  sat_guarded_non_collapsed_types:        0
% 3.77/1.01  num_pure_diseq_elim:                    0
% 3.77/1.01  simp_replaced_by:                       0
% 3.77/1.01  res_preprocessed:                       175
% 3.77/1.01  prep_upred:                             0
% 3.77/1.01  prep_unflattend:                        49
% 3.77/1.01  smt_new_axioms:                         0
% 3.77/1.01  pred_elim_cands:                        4
% 3.77/1.01  pred_elim:                              2
% 3.77/1.01  pred_elim_cl:                           0
% 3.77/1.01  pred_elim_cycles:                       5
% 3.77/1.01  merged_defs:                            8
% 3.77/1.01  merged_defs_ncl:                        0
% 3.77/1.01  bin_hyper_res:                          9
% 3.77/1.01  prep_cycles:                            4
% 3.77/1.01  pred_elim_time:                         0.015
% 3.77/1.01  splitting_time:                         0.
% 3.77/1.01  sem_filter_time:                        0.
% 3.77/1.01  monotx_time:                            0.001
% 3.77/1.01  subtype_inf_time:                       0.
% 3.77/1.01  
% 3.77/1.01  ------ Problem properties
% 3.77/1.01  
% 3.77/1.01  clauses:                                38
% 3.77/1.01  conjectures:                            4
% 3.77/1.01  epr:                                    8
% 3.77/1.01  horn:                                   33
% 3.77/1.01  ground:                                 14
% 3.77/1.01  unary:                                  10
% 3.77/1.01  binary:                                 9
% 3.77/1.01  lits:                                   99
% 3.77/1.01  lits_eq:                                36
% 3.77/1.01  fd_pure:                                0
% 3.77/1.01  fd_pseudo:                              0
% 3.77/1.01  fd_cond:                                3
% 3.77/1.01  fd_pseudo_cond:                         1
% 3.77/1.01  ac_symbols:                             0
% 3.77/1.01  
% 3.77/1.01  ------ Propositional Solver
% 3.77/1.01  
% 3.77/1.01  prop_solver_calls:                      27
% 3.77/1.01  prop_fast_solver_calls:                 1438
% 3.77/1.01  smt_solver_calls:                       0
% 3.77/1.01  smt_fast_solver_calls:                  0
% 3.77/1.01  prop_num_of_clauses:                    3957
% 3.77/1.01  prop_preprocess_simplified:             10786
% 3.77/1.01  prop_fo_subsumed:                       39
% 3.77/1.01  prop_solver_time:                       0.
% 3.77/1.01  smt_solver_time:                        0.
% 3.77/1.01  smt_fast_solver_time:                   0.
% 3.77/1.01  prop_fast_solver_time:                  0.
% 3.77/1.01  prop_unsat_core_time:                   0.
% 3.77/1.01  
% 3.77/1.01  ------ QBF
% 3.77/1.01  
% 3.77/1.01  qbf_q_res:                              0
% 3.77/1.01  qbf_num_tautologies:                    0
% 3.77/1.01  qbf_prep_cycles:                        0
% 3.77/1.01  
% 3.77/1.01  ------ BMC1
% 3.77/1.01  
% 3.77/1.01  bmc1_current_bound:                     -1
% 3.77/1.01  bmc1_last_solved_bound:                 -1
% 3.77/1.01  bmc1_unsat_core_size:                   -1
% 3.77/1.01  bmc1_unsat_core_parents_size:           -1
% 3.77/1.01  bmc1_merge_next_fun:                    0
% 3.77/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.77/1.01  
% 3.77/1.01  ------ Instantiation
% 3.77/1.01  
% 3.77/1.01  inst_num_of_clauses:                    1040
% 3.77/1.01  inst_num_in_passive:                    351
% 3.77/1.01  inst_num_in_active:                     503
% 3.77/1.01  inst_num_in_unprocessed:                186
% 3.77/1.01  inst_num_of_loops:                      660
% 3.77/1.01  inst_num_of_learning_restarts:          0
% 3.77/1.01  inst_num_moves_active_passive:          156
% 3.77/1.01  inst_lit_activity:                      0
% 3.77/1.01  inst_lit_activity_moves:                0
% 3.77/1.01  inst_num_tautologies:                   0
% 3.77/1.01  inst_num_prop_implied:                  0
% 3.77/1.01  inst_num_existing_simplified:           0
% 3.77/1.01  inst_num_eq_res_simplified:             0
% 3.77/1.01  inst_num_child_elim:                    0
% 3.77/1.01  inst_num_of_dismatching_blockings:      316
% 3.77/1.01  inst_num_of_non_proper_insts:           920
% 3.77/1.01  inst_num_of_duplicates:                 0
% 3.77/1.01  inst_inst_num_from_inst_to_res:         0
% 3.77/1.01  inst_dismatching_checking_time:         0.
% 3.77/1.01  
% 3.77/1.01  ------ Resolution
% 3.77/1.01  
% 3.77/1.01  res_num_of_clauses:                     0
% 3.77/1.01  res_num_in_passive:                     0
% 3.77/1.01  res_num_in_active:                      0
% 3.77/1.01  res_num_of_loops:                       179
% 3.77/1.01  res_forward_subset_subsumed:            48
% 3.77/1.01  res_backward_subset_subsumed:           0
% 3.77/1.01  res_forward_subsumed:                   0
% 3.77/1.01  res_backward_subsumed:                  0
% 3.77/1.01  res_forward_subsumption_resolution:     6
% 3.77/1.01  res_backward_subsumption_resolution:    0
% 3.77/1.01  res_clause_to_clause_subsumption:       991
% 3.77/1.01  res_orphan_elimination:                 0
% 3.77/1.01  res_tautology_del:                      90
% 3.77/1.01  res_num_eq_res_simplified:              1
% 3.77/1.01  res_num_sel_changes:                    0
% 3.77/1.01  res_moves_from_active_to_pass:          0
% 3.77/1.01  
% 3.77/1.01  ------ Superposition
% 3.77/1.01  
% 3.77/1.01  sup_time_total:                         0.
% 3.77/1.01  sup_time_generating:                    0.
% 3.77/1.01  sup_time_sim_full:                      0.
% 3.77/1.01  sup_time_sim_immed:                     0.
% 3.77/1.01  
% 3.77/1.01  sup_num_of_clauses:                     190
% 3.77/1.01  sup_num_in_active:                      62
% 3.77/1.01  sup_num_in_passive:                     128
% 3.77/1.01  sup_num_of_loops:                       130
% 3.77/1.01  sup_fw_superposition:                   161
% 3.77/1.01  sup_bw_superposition:                   140
% 3.77/1.01  sup_immediate_simplified:               53
% 3.77/1.01  sup_given_eliminated:                   0
% 3.77/1.01  comparisons_done:                       0
% 3.77/1.01  comparisons_avoided:                    37
% 3.77/1.01  
% 3.77/1.01  ------ Simplifications
% 3.77/1.01  
% 3.77/1.01  
% 3.77/1.01  sim_fw_subset_subsumed:                 15
% 3.77/1.01  sim_bw_subset_subsumed:                 21
% 3.77/1.01  sim_fw_subsumed:                        19
% 3.77/1.01  sim_bw_subsumed:                        1
% 3.77/1.01  sim_fw_subsumption_res:                 9
% 3.77/1.01  sim_bw_subsumption_res:                 3
% 3.77/1.01  sim_tautology_del:                      7
% 3.77/1.01  sim_eq_tautology_del:                   13
% 3.77/1.01  sim_eq_res_simp:                        3
% 3.77/1.01  sim_fw_demodulated:                     17
% 3.77/1.01  sim_bw_demodulated:                     62
% 3.77/1.01  sim_light_normalised:                   28
% 3.77/1.01  sim_joinable_taut:                      0
% 3.77/1.01  sim_joinable_simp:                      0
% 3.77/1.01  sim_ac_normalised:                      0
% 3.77/1.01  sim_smt_subsumption:                    0
% 3.77/1.01  
%------------------------------------------------------------------------------
