%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:53 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  213 (6659 expanded)
%              Number of clauses        :  140 (2172 expanded)
%              Number of leaves         :   19 (1250 expanded)
%              Depth                    :   27
%              Number of atoms          :  646 (37189 expanded)
%              Number of equality atoms :  348 (9952 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2083,plain,
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

cnf(c_2082,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2088,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4082,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2082,c_2088])).

cnf(c_4230,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_753,c_4082])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2092,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6069,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_2092])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2388,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_7973,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6069,c_42,c_2388])).

cnf(c_7974,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7973])).

cnf(c_7984,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2083,c_7974])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8008,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7984,c_2084])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2085,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8617,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2082,c_2085])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2468,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2551,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2468])).

cnf(c_8787,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8617,c_39,c_37,c_2551])).

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

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_449,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_19])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_449])).

cnf(c_774,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_762,c_19,c_450])).

cnf(c_2071,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_8794,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8787,c_2071])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2086,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6357,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2082,c_2086])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2449,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2543,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_2544,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2543])).

cnf(c_6407,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6357,c_40,c_42,c_2544])).

cnf(c_8796,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8787,c_6407])).

cnf(c_8810,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8794,c_8796])).

cnf(c_11333,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7984,c_8810])).

cnf(c_11339,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8008,c_11333])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8845,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8787,c_2087])).

cnf(c_8920,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8845,c_40,c_42])).

cnf(c_2089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8934,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8920,c_2089])).

cnf(c_2080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_8933,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8920,c_2080])).

cnf(c_18820,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11339,c_8934,c_8796,c_8933])).

cnf(c_779,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_779])).

cnf(c_2070,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_8793,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8787,c_2070])).

cnf(c_8817,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8793,c_8796])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_115,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_116,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1373,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2428,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_2429,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(c_2427,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_2715,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_1372,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2716,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_3470,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_3471,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3470])).

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

cnf(c_2079,plain,
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

cnf(c_2644,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_2645,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_2660,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_40,c_42,c_599,c_2645])).

cnf(c_2661,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2660])).

cnf(c_8792,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8787,c_2661])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2411,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2588,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4284,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1374,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2568,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_2942,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_4355,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_9001,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8792,c_36,c_35,c_115,c_116,c_2411,c_2588,c_3471,c_4284,c_4355,c_7984,c_8810])).

cnf(c_15351,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8817,c_35,c_115,c_116,c_2429,c_2715,c_2716,c_3471,c_9001,c_11333])).

cnf(c_18842,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18820,c_15351])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_19138,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18842,c_5])).

cnf(c_18908,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18820,c_35])).

cnf(c_18909,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_18908])).

cnf(c_19303,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18909,c_2083])).

cnf(c_2097,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2100,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5149,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2100])).

cnf(c_19540,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19303,c_5149])).

cnf(c_18902,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_18820,c_4082])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_695,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_2074,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_2181,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2074,c_6])).

cnf(c_18905,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18820,c_2181])).

cnf(c_18916,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18905,c_18909])).

cnf(c_18917,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18916])).

cnf(c_18907,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18820,c_2082])).

cnf(c_18912,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18907,c_18909])).

cnf(c_18914,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18912,c_6])).

cnf(c_18920,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18917,c_18914])).

cnf(c_18927,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18902,c_18909,c_18920])).

cnf(c_3417,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2082,c_2089])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2091,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3438,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3417,c_2091])).

cnf(c_20043,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_18927,c_3438])).

cnf(c_22325,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19138,c_19540,c_20043])).

cnf(c_22326,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_22325])).

cnf(c_22328,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22326,c_18914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.47/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.49  
% 7.47/1.49  ------  iProver source info
% 7.47/1.49  
% 7.47/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.49  git: non_committed_changes: false
% 7.47/1.49  git: last_make_outside_of_git: false
% 7.47/1.49  
% 7.47/1.49  ------ 
% 7.47/1.49  
% 7.47/1.49  ------ Input Options
% 7.47/1.49  
% 7.47/1.49  --out_options                           all
% 7.47/1.49  --tptp_safe_out                         true
% 7.47/1.49  --problem_path                          ""
% 7.47/1.49  --include_path                          ""
% 7.47/1.49  --clausifier                            res/vclausify_rel
% 7.47/1.49  --clausifier_options                    --mode clausify
% 7.47/1.49  --stdin                                 false
% 7.47/1.49  --stats_out                             all
% 7.47/1.49  
% 7.47/1.49  ------ General Options
% 7.47/1.49  
% 7.47/1.49  --fof                                   false
% 7.47/1.49  --time_out_real                         305.
% 7.47/1.49  --time_out_virtual                      -1.
% 7.47/1.49  --symbol_type_check                     false
% 7.47/1.49  --clausify_out                          false
% 7.47/1.49  --sig_cnt_out                           false
% 7.47/1.49  --trig_cnt_out                          false
% 7.47/1.49  --trig_cnt_out_tolerance                1.
% 7.47/1.49  --trig_cnt_out_sk_spl                   false
% 7.47/1.49  --abstr_cl_out                          false
% 7.47/1.49  
% 7.47/1.49  ------ Global Options
% 7.47/1.49  
% 7.47/1.49  --schedule                              default
% 7.47/1.49  --add_important_lit                     false
% 7.47/1.49  --prop_solver_per_cl                    1000
% 7.47/1.49  --min_unsat_core                        false
% 7.47/1.49  --soft_assumptions                      false
% 7.47/1.49  --soft_lemma_size                       3
% 7.47/1.49  --prop_impl_unit_size                   0
% 7.47/1.49  --prop_impl_unit                        []
% 7.47/1.49  --share_sel_clauses                     true
% 7.47/1.49  --reset_solvers                         false
% 7.47/1.49  --bc_imp_inh                            [conj_cone]
% 7.47/1.49  --conj_cone_tolerance                   3.
% 7.47/1.49  --extra_neg_conj                        none
% 7.47/1.49  --large_theory_mode                     true
% 7.47/1.49  --prolific_symb_bound                   200
% 7.47/1.49  --lt_threshold                          2000
% 7.47/1.49  --clause_weak_htbl                      true
% 7.47/1.49  --gc_record_bc_elim                     false
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing Options
% 7.47/1.49  
% 7.47/1.49  --preprocessing_flag                    true
% 7.47/1.49  --time_out_prep_mult                    0.1
% 7.47/1.49  --splitting_mode                        input
% 7.47/1.49  --splitting_grd                         true
% 7.47/1.49  --splitting_cvd                         false
% 7.47/1.49  --splitting_cvd_svl                     false
% 7.47/1.49  --splitting_nvd                         32
% 7.47/1.49  --sub_typing                            true
% 7.47/1.49  --prep_gs_sim                           true
% 7.47/1.49  --prep_unflatten                        true
% 7.47/1.49  --prep_res_sim                          true
% 7.47/1.49  --prep_upred                            true
% 7.47/1.49  --prep_sem_filter                       exhaustive
% 7.47/1.49  --prep_sem_filter_out                   false
% 7.47/1.49  --pred_elim                             true
% 7.47/1.49  --res_sim_input                         true
% 7.47/1.49  --eq_ax_congr_red                       true
% 7.47/1.49  --pure_diseq_elim                       true
% 7.47/1.49  --brand_transform                       false
% 7.47/1.49  --non_eq_to_eq                          false
% 7.47/1.49  --prep_def_merge                        true
% 7.47/1.49  --prep_def_merge_prop_impl              false
% 7.47/1.49  --prep_def_merge_mbd                    true
% 7.47/1.49  --prep_def_merge_tr_red                 false
% 7.47/1.49  --prep_def_merge_tr_cl                  false
% 7.47/1.49  --smt_preprocessing                     true
% 7.47/1.49  --smt_ac_axioms                         fast
% 7.47/1.49  --preprocessed_out                      false
% 7.47/1.49  --preprocessed_stats                    false
% 7.47/1.49  
% 7.47/1.49  ------ Abstraction refinement Options
% 7.47/1.49  
% 7.47/1.49  --abstr_ref                             []
% 7.47/1.49  --abstr_ref_prep                        false
% 7.47/1.49  --abstr_ref_until_sat                   false
% 7.47/1.49  --abstr_ref_sig_restrict                funpre
% 7.47/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.49  --abstr_ref_under                       []
% 7.47/1.49  
% 7.47/1.49  ------ SAT Options
% 7.47/1.49  
% 7.47/1.49  --sat_mode                              false
% 7.47/1.49  --sat_fm_restart_options                ""
% 7.47/1.49  --sat_gr_def                            false
% 7.47/1.49  --sat_epr_types                         true
% 7.47/1.49  --sat_non_cyclic_types                  false
% 7.47/1.49  --sat_finite_models                     false
% 7.47/1.49  --sat_fm_lemmas                         false
% 7.47/1.49  --sat_fm_prep                           false
% 7.47/1.49  --sat_fm_uc_incr                        true
% 7.47/1.49  --sat_out_model                         small
% 7.47/1.49  --sat_out_clauses                       false
% 7.47/1.49  
% 7.47/1.49  ------ QBF Options
% 7.47/1.49  
% 7.47/1.49  --qbf_mode                              false
% 7.47/1.49  --qbf_elim_univ                         false
% 7.47/1.49  --qbf_dom_inst                          none
% 7.47/1.49  --qbf_dom_pre_inst                      false
% 7.47/1.49  --qbf_sk_in                             false
% 7.47/1.49  --qbf_pred_elim                         true
% 7.47/1.49  --qbf_split                             512
% 7.47/1.49  
% 7.47/1.49  ------ BMC1 Options
% 7.47/1.49  
% 7.47/1.49  --bmc1_incremental                      false
% 7.47/1.49  --bmc1_axioms                           reachable_all
% 7.47/1.49  --bmc1_min_bound                        0
% 7.47/1.49  --bmc1_max_bound                        -1
% 7.47/1.49  --bmc1_max_bound_default                -1
% 7.47/1.49  --bmc1_symbol_reachability              true
% 7.47/1.49  --bmc1_property_lemmas                  false
% 7.47/1.49  --bmc1_k_induction                      false
% 7.47/1.49  --bmc1_non_equiv_states                 false
% 7.47/1.49  --bmc1_deadlock                         false
% 7.47/1.49  --bmc1_ucm                              false
% 7.47/1.49  --bmc1_add_unsat_core                   none
% 7.47/1.49  --bmc1_unsat_core_children              false
% 7.47/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.49  --bmc1_out_stat                         full
% 7.47/1.49  --bmc1_ground_init                      false
% 7.47/1.49  --bmc1_pre_inst_next_state              false
% 7.47/1.49  --bmc1_pre_inst_state                   false
% 7.47/1.49  --bmc1_pre_inst_reach_state             false
% 7.47/1.49  --bmc1_out_unsat_core                   false
% 7.47/1.49  --bmc1_aig_witness_out                  false
% 7.47/1.49  --bmc1_verbose                          false
% 7.47/1.49  --bmc1_dump_clauses_tptp                false
% 7.47/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.49  --bmc1_dump_file                        -
% 7.47/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.49  --bmc1_ucm_extend_mode                  1
% 7.47/1.49  --bmc1_ucm_init_mode                    2
% 7.47/1.49  --bmc1_ucm_cone_mode                    none
% 7.47/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.49  --bmc1_ucm_relax_model                  4
% 7.47/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.49  --bmc1_ucm_layered_model                none
% 7.47/1.49  --bmc1_ucm_max_lemma_size               10
% 7.47/1.49  
% 7.47/1.49  ------ AIG Options
% 7.47/1.49  
% 7.47/1.49  --aig_mode                              false
% 7.47/1.49  
% 7.47/1.49  ------ Instantiation Options
% 7.47/1.49  
% 7.47/1.49  --instantiation_flag                    true
% 7.47/1.49  --inst_sos_flag                         false
% 7.47/1.49  --inst_sos_phase                        true
% 7.47/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.49  --inst_lit_sel_side                     num_symb
% 7.47/1.49  --inst_solver_per_active                1400
% 7.47/1.49  --inst_solver_calls_frac                1.
% 7.47/1.49  --inst_passive_queue_type               priority_queues
% 7.47/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.49  --inst_passive_queues_freq              [25;2]
% 7.47/1.49  --inst_dismatching                      true
% 7.47/1.49  --inst_eager_unprocessed_to_passive     true
% 7.47/1.49  --inst_prop_sim_given                   true
% 7.47/1.49  --inst_prop_sim_new                     false
% 7.47/1.49  --inst_subs_new                         false
% 7.47/1.49  --inst_eq_res_simp                      false
% 7.47/1.49  --inst_subs_given                       false
% 7.47/1.49  --inst_orphan_elimination               true
% 7.47/1.49  --inst_learning_loop_flag               true
% 7.47/1.49  --inst_learning_start                   3000
% 7.47/1.49  --inst_learning_factor                  2
% 7.47/1.49  --inst_start_prop_sim_after_learn       3
% 7.47/1.49  --inst_sel_renew                        solver
% 7.47/1.49  --inst_lit_activity_flag                true
% 7.47/1.49  --inst_restr_to_given                   false
% 7.47/1.49  --inst_activity_threshold               500
% 7.47/1.49  --inst_out_proof                        true
% 7.47/1.49  
% 7.47/1.49  ------ Resolution Options
% 7.47/1.49  
% 7.47/1.49  --resolution_flag                       true
% 7.47/1.49  --res_lit_sel                           adaptive
% 7.47/1.49  --res_lit_sel_side                      none
% 7.47/1.49  --res_ordering                          kbo
% 7.47/1.49  --res_to_prop_solver                    active
% 7.47/1.49  --res_prop_simpl_new                    false
% 7.47/1.49  --res_prop_simpl_given                  true
% 7.47/1.49  --res_passive_queue_type                priority_queues
% 7.47/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.49  --res_passive_queues_freq               [15;5]
% 7.47/1.49  --res_forward_subs                      full
% 7.47/1.49  --res_backward_subs                     full
% 7.47/1.49  --res_forward_subs_resolution           true
% 7.47/1.49  --res_backward_subs_resolution          true
% 7.47/1.49  --res_orphan_elimination                true
% 7.47/1.49  --res_time_limit                        2.
% 7.47/1.49  --res_out_proof                         true
% 7.47/1.49  
% 7.47/1.49  ------ Superposition Options
% 7.47/1.49  
% 7.47/1.49  --superposition_flag                    true
% 7.47/1.49  --sup_passive_queue_type                priority_queues
% 7.47/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.49  --demod_completeness_check              fast
% 7.47/1.49  --demod_use_ground                      true
% 7.47/1.49  --sup_to_prop_solver                    passive
% 7.47/1.49  --sup_prop_simpl_new                    true
% 7.47/1.49  --sup_prop_simpl_given                  true
% 7.47/1.49  --sup_fun_splitting                     false
% 7.47/1.49  --sup_smt_interval                      50000
% 7.47/1.49  
% 7.47/1.49  ------ Superposition Simplification Setup
% 7.47/1.49  
% 7.47/1.49  --sup_indices_passive                   []
% 7.47/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_full_bw                           [BwDemod]
% 7.47/1.49  --sup_immed_triv                        [TrivRules]
% 7.47/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_immed_bw_main                     []
% 7.47/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.49  
% 7.47/1.49  ------ Combination Options
% 7.47/1.49  
% 7.47/1.49  --comb_res_mult                         3
% 7.47/1.49  --comb_sup_mult                         2
% 7.47/1.49  --comb_inst_mult                        10
% 7.47/1.49  
% 7.47/1.49  ------ Debug Options
% 7.47/1.49  
% 7.47/1.49  --dbg_backtrace                         false
% 7.47/1.49  --dbg_dump_prop_clauses                 false
% 7.47/1.49  --dbg_dump_prop_clauses_file            -
% 7.47/1.49  --dbg_out_stat                          false
% 7.47/1.49  ------ Parsing...
% 7.47/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  ------ Proving...
% 7.47/1.49  ------ Problem Properties 
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  clauses                                 38
% 7.47/1.49  conjectures                             4
% 7.47/1.49  EPR                                     7
% 7.47/1.49  Horn                                    33
% 7.47/1.49  unary                                   10
% 7.47/1.49  binary                                  9
% 7.47/1.49  lits                                    98
% 7.47/1.49  lits eq                                 38
% 7.47/1.49  fd_pure                                 0
% 7.47/1.49  fd_pseudo                               0
% 7.47/1.49  fd_cond                                 3
% 7.47/1.49  fd_pseudo_cond                          1
% 7.47/1.49  AC symbols                              0
% 7.47/1.49  
% 7.47/1.49  ------ Schedule dynamic 5 is on 
% 7.47/1.49  
% 7.47/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ 
% 7.47/1.49  Current options:
% 7.47/1.49  ------ 
% 7.47/1.49  
% 7.47/1.49  ------ Input Options
% 7.47/1.49  
% 7.47/1.49  --out_options                           all
% 7.47/1.49  --tptp_safe_out                         true
% 7.47/1.49  --problem_path                          ""
% 7.47/1.49  --include_path                          ""
% 7.47/1.49  --clausifier                            res/vclausify_rel
% 7.47/1.49  --clausifier_options                    --mode clausify
% 7.47/1.49  --stdin                                 false
% 7.47/1.49  --stats_out                             all
% 7.47/1.49  
% 7.47/1.49  ------ General Options
% 7.47/1.49  
% 7.47/1.49  --fof                                   false
% 7.47/1.49  --time_out_real                         305.
% 7.47/1.49  --time_out_virtual                      -1.
% 7.47/1.49  --symbol_type_check                     false
% 7.47/1.49  --clausify_out                          false
% 7.47/1.49  --sig_cnt_out                           false
% 7.47/1.49  --trig_cnt_out                          false
% 7.47/1.49  --trig_cnt_out_tolerance                1.
% 7.47/1.49  --trig_cnt_out_sk_spl                   false
% 7.47/1.49  --abstr_cl_out                          false
% 7.47/1.49  
% 7.47/1.49  ------ Global Options
% 7.47/1.49  
% 7.47/1.49  --schedule                              default
% 7.47/1.49  --add_important_lit                     false
% 7.47/1.49  --prop_solver_per_cl                    1000
% 7.47/1.49  --min_unsat_core                        false
% 7.47/1.49  --soft_assumptions                      false
% 7.47/1.49  --soft_lemma_size                       3
% 7.47/1.49  --prop_impl_unit_size                   0
% 7.47/1.49  --prop_impl_unit                        []
% 7.47/1.49  --share_sel_clauses                     true
% 7.47/1.49  --reset_solvers                         false
% 7.47/1.49  --bc_imp_inh                            [conj_cone]
% 7.47/1.49  --conj_cone_tolerance                   3.
% 7.47/1.49  --extra_neg_conj                        none
% 7.47/1.49  --large_theory_mode                     true
% 7.47/1.49  --prolific_symb_bound                   200
% 7.47/1.49  --lt_threshold                          2000
% 7.47/1.49  --clause_weak_htbl                      true
% 7.47/1.49  --gc_record_bc_elim                     false
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing Options
% 7.47/1.49  
% 7.47/1.49  --preprocessing_flag                    true
% 7.47/1.49  --time_out_prep_mult                    0.1
% 7.47/1.49  --splitting_mode                        input
% 7.47/1.49  --splitting_grd                         true
% 7.47/1.49  --splitting_cvd                         false
% 7.47/1.49  --splitting_cvd_svl                     false
% 7.47/1.49  --splitting_nvd                         32
% 7.47/1.49  --sub_typing                            true
% 7.47/1.49  --prep_gs_sim                           true
% 7.47/1.49  --prep_unflatten                        true
% 7.47/1.49  --prep_res_sim                          true
% 7.47/1.49  --prep_upred                            true
% 7.47/1.49  --prep_sem_filter                       exhaustive
% 7.47/1.49  --prep_sem_filter_out                   false
% 7.47/1.49  --pred_elim                             true
% 7.47/1.49  --res_sim_input                         true
% 7.47/1.49  --eq_ax_congr_red                       true
% 7.47/1.49  --pure_diseq_elim                       true
% 7.47/1.49  --brand_transform                       false
% 7.47/1.49  --non_eq_to_eq                          false
% 7.47/1.49  --prep_def_merge                        true
% 7.47/1.49  --prep_def_merge_prop_impl              false
% 7.47/1.49  --prep_def_merge_mbd                    true
% 7.47/1.49  --prep_def_merge_tr_red                 false
% 7.47/1.49  --prep_def_merge_tr_cl                  false
% 7.47/1.49  --smt_preprocessing                     true
% 7.47/1.49  --smt_ac_axioms                         fast
% 7.47/1.49  --preprocessed_out                      false
% 7.47/1.49  --preprocessed_stats                    false
% 7.47/1.49  
% 7.47/1.49  ------ Abstraction refinement Options
% 7.47/1.49  
% 7.47/1.49  --abstr_ref                             []
% 7.47/1.49  --abstr_ref_prep                        false
% 7.47/1.49  --abstr_ref_until_sat                   false
% 7.47/1.49  --abstr_ref_sig_restrict                funpre
% 7.47/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.49  --abstr_ref_under                       []
% 7.47/1.49  
% 7.47/1.49  ------ SAT Options
% 7.47/1.49  
% 7.47/1.49  --sat_mode                              false
% 7.47/1.49  --sat_fm_restart_options                ""
% 7.47/1.49  --sat_gr_def                            false
% 7.47/1.49  --sat_epr_types                         true
% 7.47/1.49  --sat_non_cyclic_types                  false
% 7.47/1.49  --sat_finite_models                     false
% 7.47/1.49  --sat_fm_lemmas                         false
% 7.47/1.49  --sat_fm_prep                           false
% 7.47/1.49  --sat_fm_uc_incr                        true
% 7.47/1.49  --sat_out_model                         small
% 7.47/1.49  --sat_out_clauses                       false
% 7.47/1.49  
% 7.47/1.49  ------ QBF Options
% 7.47/1.49  
% 7.47/1.49  --qbf_mode                              false
% 7.47/1.49  --qbf_elim_univ                         false
% 7.47/1.49  --qbf_dom_inst                          none
% 7.47/1.49  --qbf_dom_pre_inst                      false
% 7.47/1.49  --qbf_sk_in                             false
% 7.47/1.49  --qbf_pred_elim                         true
% 7.47/1.49  --qbf_split                             512
% 7.47/1.49  
% 7.47/1.49  ------ BMC1 Options
% 7.47/1.49  
% 7.47/1.49  --bmc1_incremental                      false
% 7.47/1.49  --bmc1_axioms                           reachable_all
% 7.47/1.49  --bmc1_min_bound                        0
% 7.47/1.49  --bmc1_max_bound                        -1
% 7.47/1.49  --bmc1_max_bound_default                -1
% 7.47/1.49  --bmc1_symbol_reachability              true
% 7.47/1.49  --bmc1_property_lemmas                  false
% 7.47/1.49  --bmc1_k_induction                      false
% 7.47/1.49  --bmc1_non_equiv_states                 false
% 7.47/1.49  --bmc1_deadlock                         false
% 7.47/1.49  --bmc1_ucm                              false
% 7.47/1.49  --bmc1_add_unsat_core                   none
% 7.47/1.49  --bmc1_unsat_core_children              false
% 7.47/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.49  --bmc1_out_stat                         full
% 7.47/1.49  --bmc1_ground_init                      false
% 7.47/1.49  --bmc1_pre_inst_next_state              false
% 7.47/1.49  --bmc1_pre_inst_state                   false
% 7.47/1.49  --bmc1_pre_inst_reach_state             false
% 7.47/1.49  --bmc1_out_unsat_core                   false
% 7.47/1.49  --bmc1_aig_witness_out                  false
% 7.47/1.49  --bmc1_verbose                          false
% 7.47/1.49  --bmc1_dump_clauses_tptp                false
% 7.47/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.49  --bmc1_dump_file                        -
% 7.47/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.49  --bmc1_ucm_extend_mode                  1
% 7.47/1.49  --bmc1_ucm_init_mode                    2
% 7.47/1.49  --bmc1_ucm_cone_mode                    none
% 7.47/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.49  --bmc1_ucm_relax_model                  4
% 7.47/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.49  --bmc1_ucm_layered_model                none
% 7.47/1.49  --bmc1_ucm_max_lemma_size               10
% 7.47/1.49  
% 7.47/1.49  ------ AIG Options
% 7.47/1.49  
% 7.47/1.49  --aig_mode                              false
% 7.47/1.49  
% 7.47/1.49  ------ Instantiation Options
% 7.47/1.49  
% 7.47/1.49  --instantiation_flag                    true
% 7.47/1.49  --inst_sos_flag                         false
% 7.47/1.49  --inst_sos_phase                        true
% 7.47/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.49  --inst_lit_sel_side                     none
% 7.47/1.49  --inst_solver_per_active                1400
% 7.47/1.49  --inst_solver_calls_frac                1.
% 7.47/1.49  --inst_passive_queue_type               priority_queues
% 7.47/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.49  --inst_passive_queues_freq              [25;2]
% 7.47/1.49  --inst_dismatching                      true
% 7.47/1.49  --inst_eager_unprocessed_to_passive     true
% 7.47/1.49  --inst_prop_sim_given                   true
% 7.47/1.49  --inst_prop_sim_new                     false
% 7.47/1.49  --inst_subs_new                         false
% 7.47/1.49  --inst_eq_res_simp                      false
% 7.47/1.49  --inst_subs_given                       false
% 7.47/1.49  --inst_orphan_elimination               true
% 7.47/1.49  --inst_learning_loop_flag               true
% 7.47/1.49  --inst_learning_start                   3000
% 7.47/1.49  --inst_learning_factor                  2
% 7.47/1.49  --inst_start_prop_sim_after_learn       3
% 7.47/1.49  --inst_sel_renew                        solver
% 7.47/1.49  --inst_lit_activity_flag                true
% 7.47/1.49  --inst_restr_to_given                   false
% 7.47/1.49  --inst_activity_threshold               500
% 7.47/1.49  --inst_out_proof                        true
% 7.47/1.49  
% 7.47/1.49  ------ Resolution Options
% 7.47/1.49  
% 7.47/1.49  --resolution_flag                       false
% 7.47/1.49  --res_lit_sel                           adaptive
% 7.47/1.49  --res_lit_sel_side                      none
% 7.47/1.49  --res_ordering                          kbo
% 7.47/1.49  --res_to_prop_solver                    active
% 7.47/1.49  --res_prop_simpl_new                    false
% 7.47/1.49  --res_prop_simpl_given                  true
% 7.47/1.49  --res_passive_queue_type                priority_queues
% 7.47/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.49  --res_passive_queues_freq               [15;5]
% 7.47/1.49  --res_forward_subs                      full
% 7.47/1.49  --res_backward_subs                     full
% 7.47/1.49  --res_forward_subs_resolution           true
% 7.47/1.49  --res_backward_subs_resolution          true
% 7.47/1.49  --res_orphan_elimination                true
% 7.47/1.49  --res_time_limit                        2.
% 7.47/1.49  --res_out_proof                         true
% 7.47/1.49  
% 7.47/1.49  ------ Superposition Options
% 7.47/1.49  
% 7.47/1.49  --superposition_flag                    true
% 7.47/1.49  --sup_passive_queue_type                priority_queues
% 7.47/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.49  --demod_completeness_check              fast
% 7.47/1.49  --demod_use_ground                      true
% 7.47/1.49  --sup_to_prop_solver                    passive
% 7.47/1.49  --sup_prop_simpl_new                    true
% 7.47/1.49  --sup_prop_simpl_given                  true
% 7.47/1.49  --sup_fun_splitting                     false
% 7.47/1.49  --sup_smt_interval                      50000
% 7.47/1.49  
% 7.47/1.49  ------ Superposition Simplification Setup
% 7.47/1.49  
% 7.47/1.49  --sup_indices_passive                   []
% 7.47/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_full_bw                           [BwDemod]
% 7.47/1.49  --sup_immed_triv                        [TrivRules]
% 7.47/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_immed_bw_main                     []
% 7.47/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.49  
% 7.47/1.49  ------ Combination Options
% 7.47/1.49  
% 7.47/1.49  --comb_res_mult                         3
% 7.47/1.49  --comb_sup_mult                         2
% 7.47/1.49  --comb_inst_mult                        10
% 7.47/1.49  
% 7.47/1.49  ------ Debug Options
% 7.47/1.49  
% 7.47/1.49  --dbg_backtrace                         false
% 7.47/1.49  --dbg_dump_prop_clauses                 false
% 7.47/1.49  --dbg_dump_prop_clauses_file            -
% 7.47/1.49  --dbg_out_stat                          false
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  % SZS status Theorem for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49   Resolution empty clause
% 7.47/1.49  
% 7.47/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  fof(f21,conjecture,(
% 7.47/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f22,negated_conjecture,(
% 7.47/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.47/1.49    inference(negated_conjecture,[],[f21])).
% 7.47/1.49  
% 7.47/1.49  fof(f45,plain,(
% 7.47/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.47/1.49    inference(ennf_transformation,[],[f22])).
% 7.47/1.49  
% 7.47/1.49  fof(f46,plain,(
% 7.47/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.47/1.49    inference(flattening,[],[f45])).
% 7.47/1.49  
% 7.47/1.49  fof(f54,plain,(
% 7.47/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.47/1.49    introduced(choice_axiom,[])).
% 7.47/1.49  
% 7.47/1.49  fof(f55,plain,(
% 7.47/1.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.47/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f54])).
% 7.47/1.49  
% 7.47/1.49  fof(f93,plain,(
% 7.47/1.49    r1_tarski(sK2,sK0)),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f17,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f37,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(ennf_transformation,[],[f17])).
% 7.47/1.49  
% 7.47/1.49  fof(f38,plain,(
% 7.47/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(flattening,[],[f37])).
% 7.47/1.49  
% 7.47/1.49  fof(f53,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(nnf_transformation,[],[f38])).
% 7.47/1.49  
% 7.47/1.49  fof(f78,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f53])).
% 7.47/1.49  
% 7.47/1.49  fof(f91,plain,(
% 7.47/1.49    v1_funct_2(sK3,sK0,sK1)),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f92,plain,(
% 7.47/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f16,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f36,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(ennf_transformation,[],[f16])).
% 7.47/1.49  
% 7.47/1.49  fof(f77,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f36])).
% 7.47/1.49  
% 7.47/1.49  fof(f11,axiom,(
% 7.47/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f30,plain,(
% 7.47/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.47/1.49    inference(ennf_transformation,[],[f11])).
% 7.47/1.49  
% 7.47/1.49  fof(f31,plain,(
% 7.47/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.47/1.49    inference(flattening,[],[f30])).
% 7.47/1.49  
% 7.47/1.49  fof(f72,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f31])).
% 7.47/1.49  
% 7.47/1.49  fof(f14,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f34,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(ennf_transformation,[],[f14])).
% 7.47/1.49  
% 7.47/1.49  fof(f75,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f34])).
% 7.47/1.49  
% 7.47/1.49  fof(f20,axiom,(
% 7.47/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f43,plain,(
% 7.47/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.47/1.49    inference(ennf_transformation,[],[f20])).
% 7.47/1.49  
% 7.47/1.49  fof(f44,plain,(
% 7.47/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.47/1.49    inference(flattening,[],[f43])).
% 7.47/1.49  
% 7.47/1.49  fof(f89,plain,(
% 7.47/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f44])).
% 7.47/1.49  
% 7.47/1.49  fof(f19,axiom,(
% 7.47/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f41,plain,(
% 7.47/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.47/1.49    inference(ennf_transformation,[],[f19])).
% 7.47/1.49  
% 7.47/1.49  fof(f42,plain,(
% 7.47/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.47/1.49    inference(flattening,[],[f41])).
% 7.47/1.49  
% 7.47/1.49  fof(f86,plain,(
% 7.47/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f42])).
% 7.47/1.49  
% 7.47/1.49  fof(f90,plain,(
% 7.47/1.49    v1_funct_1(sK3)),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f88,plain,(
% 7.47/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f44])).
% 7.47/1.49  
% 7.47/1.49  fof(f95,plain,(
% 7.47/1.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f15,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f23,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.47/1.49    inference(pure_predicate_removal,[],[f15])).
% 7.47/1.49  
% 7.47/1.49  fof(f35,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.49    inference(ennf_transformation,[],[f23])).
% 7.47/1.49  
% 7.47/1.49  fof(f76,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f35])).
% 7.47/1.49  
% 7.47/1.49  fof(f8,axiom,(
% 7.47/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f27,plain,(
% 7.47/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.47/1.49    inference(ennf_transformation,[],[f8])).
% 7.47/1.49  
% 7.47/1.49  fof(f52,plain,(
% 7.47/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.47/1.49    inference(nnf_transformation,[],[f27])).
% 7.47/1.49  
% 7.47/1.49  fof(f67,plain,(
% 7.47/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f52])).
% 7.47/1.49  
% 7.47/1.49  fof(f18,axiom,(
% 7.47/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f39,plain,(
% 7.47/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.47/1.49    inference(ennf_transformation,[],[f18])).
% 7.47/1.49  
% 7.47/1.49  fof(f40,plain,(
% 7.47/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.47/1.49    inference(flattening,[],[f39])).
% 7.47/1.49  
% 7.47/1.49  fof(f84,plain,(
% 7.47/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f40])).
% 7.47/1.49  
% 7.47/1.49  fof(f85,plain,(
% 7.47/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f40])).
% 7.47/1.49  
% 7.47/1.49  fof(f94,plain,(
% 7.47/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.47/1.49    inference(cnf_transformation,[],[f55])).
% 7.47/1.49  
% 7.47/1.49  fof(f4,axiom,(
% 7.47/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f49,plain,(
% 7.47/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.47/1.49    inference(nnf_transformation,[],[f4])).
% 7.47/1.49  
% 7.47/1.49  fof(f50,plain,(
% 7.47/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.47/1.49    inference(flattening,[],[f49])).
% 7.47/1.49  
% 7.47/1.49  fof(f61,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f50])).
% 7.47/1.49  
% 7.47/1.49  fof(f62,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.47/1.49    inference(cnf_transformation,[],[f50])).
% 7.47/1.49  
% 7.47/1.49  fof(f99,plain,(
% 7.47/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.47/1.49    inference(equality_resolution,[],[f62])).
% 7.47/1.49  
% 7.47/1.49  fof(f83,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f53])).
% 7.47/1.49  
% 7.47/1.49  fof(f100,plain,(
% 7.47/1.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(equality_resolution,[],[f83])).
% 7.47/1.49  
% 7.47/1.49  fof(f101,plain,(
% 7.47/1.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.47/1.49    inference(equality_resolution,[],[f100])).
% 7.47/1.49  
% 7.47/1.49  fof(f5,axiom,(
% 7.47/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f64,plain,(
% 7.47/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f5])).
% 7.47/1.49  
% 7.47/1.49  fof(f1,axiom,(
% 7.47/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f47,plain,(
% 7.47/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.49    inference(nnf_transformation,[],[f1])).
% 7.47/1.49  
% 7.47/1.49  fof(f48,plain,(
% 7.47/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.49    inference(flattening,[],[f47])).
% 7.47/1.49  
% 7.47/1.49  fof(f58,plain,(
% 7.47/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f48])).
% 7.47/1.49  
% 7.47/1.49  fof(f3,axiom,(
% 7.47/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f60,plain,(
% 7.47/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f3])).
% 7.47/1.49  
% 7.47/1.49  fof(f63,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.47/1.49    inference(cnf_transformation,[],[f50])).
% 7.47/1.49  
% 7.47/1.49  fof(f98,plain,(
% 7.47/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.47/1.49    inference(equality_resolution,[],[f63])).
% 7.47/1.49  
% 7.47/1.49  fof(f79,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f53])).
% 7.47/1.49  
% 7.47/1.49  fof(f104,plain,(
% 7.47/1.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.47/1.49    inference(equality_resolution,[],[f79])).
% 7.47/1.49  
% 7.47/1.49  fof(f12,axiom,(
% 7.47/1.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.47/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f32,plain,(
% 7.47/1.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.47/1.49    inference(ennf_transformation,[],[f12])).
% 7.47/1.49  
% 7.47/1.49  fof(f73,plain,(
% 7.47/1.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f32])).
% 7.47/1.49  
% 7.47/1.49  cnf(c_36,negated_conjecture,
% 7.47/1.49      ( r1_tarski(sK2,sK0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2083,plain,
% 7.47/1.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_27,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.47/1.49      | k1_xboole_0 = X2 ),
% 7.47/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_38,negated_conjecture,
% 7.47/1.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.47/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_750,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.47/1.49      | sK3 != X0
% 7.47/1.49      | sK1 != X2
% 7.47/1.49      | sK0 != X1
% 7.47/1.49      | k1_xboole_0 = X2 ),
% 7.47/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_751,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.47/1.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.47/1.49      | k1_xboole_0 = sK1 ),
% 7.47/1.49      inference(unflattening,[status(thm)],[c_750]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_37,negated_conjecture,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.47/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_753,plain,
% 7.47/1.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.47/1.49      inference(global_propositional_subsumption,[status(thm)],[c_751,c_37]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2082,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_21,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2088,plain,
% 7.47/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.47/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4082,plain,
% 7.47/1.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2082,c_2088]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4230,plain,
% 7.47/1.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_753,c_4082]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_16,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.47/1.49      | ~ v1_relat_1(X1)
% 7.47/1.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2092,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.47/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.47/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_6069,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.47/1.49      | sK1 = k1_xboole_0
% 7.47/1.49      | r1_tarski(X0,sK0) != iProver_top
% 7.47/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_4230,c_2092]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_42,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_19,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2387,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.47/1.49      | v1_relat_1(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2388,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.47/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7973,plain,
% 7.47/1.49      ( r1_tarski(X0,sK0) != iProver_top
% 7.47/1.49      | sK1 = k1_xboole_0
% 7.47/1.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_6069,c_42,c_2388]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7974,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.47/1.49      | sK1 = k1_xboole_0
% 7.47/1.49      | r1_tarski(X0,sK0) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_7973]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7984,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2083,c_7974]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_31,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.47/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2084,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.47/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.47/1.49      | v1_funct_1(X0) != iProver_top
% 7.47/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8008,plain,
% 7.47/1.49      ( sK1 = k1_xboole_0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.47/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.47/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.47/1.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_7984,c_2084]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_30,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.47/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2085,plain,
% 7.47/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.47/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.47/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8617,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.47/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2082,c_2085]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_39,negated_conjecture,
% 7.47/1.49      ( v1_funct_1(sK3) ),
% 7.47/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2468,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.47/1.49      | ~ v1_funct_1(sK3)
% 7.47/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2551,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.47/1.49      | ~ v1_funct_1(sK3)
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2468]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8787,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_8617,c_39,c_37,c_2551]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_32,plain,
% 7.47/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.47/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_34,negated_conjecture,
% 7.47/1.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.47/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_761,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | ~ v1_relat_1(X0)
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.47/1.49      | k1_relat_1(X0) != sK2
% 7.47/1.49      | sK1 != X1 ),
% 7.47/1.49      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_762,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.47/1.49      inference(unflattening,[status(thm)],[c_761]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_20,plain,
% 7.47/1.49      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.47/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12,plain,
% 7.47/1.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_445,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.47/1.49      | ~ v1_relat_1(X0) ),
% 7.47/1.49      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_449,plain,
% 7.47/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.47/1.49      inference(global_propositional_subsumption,[status(thm)],[c_445,c_19]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_450,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_449]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_774,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.47/1.49      inference(forward_subsumption_resolution,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_762,c_19,c_450]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2071,plain,
% 7.47/1.49      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.47/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8794,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_8787,c_2071]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_29,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2086,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | v1_funct_1(X0) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_6357,plain,
% 7.47/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.47/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2082,c_2086]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_40,plain,
% 7.47/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2449,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.47/1.49      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 7.47/1.49      | ~ v1_funct_1(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2543,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 7.47/1.49      | ~ v1_funct_1(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2449]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2544,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.47/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_2543]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_6407,plain,
% 7.47/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_6357,c_40,c_42,c_2544]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8796,plain,
% 7.47/1.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_8787,c_6407]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8810,plain,
% 7.47/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_8794,c_8796]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_11333,plain,
% 7.47/1.49      ( sK1 = k1_xboole_0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_7984,c_8810]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_11339,plain,
% 7.47/1.49      ( sK1 = k1_xboole_0
% 7.47/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.47/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.47/1.49      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_8008,c_11333]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_28,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ v1_funct_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2087,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.47/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8845,plain,
% 7.47/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_8787,c_2087]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8920,plain,
% 7.47/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_8845,c_40,c_42]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2089,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8934,plain,
% 7.47/1.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_8920,c_2089]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2080,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8933,plain,
% 7.47/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_8920,c_2080]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18820,plain,
% 7.47/1.49      ( sK1 = k1_xboole_0 ),
% 7.47/1.49      inference(forward_subsumption_resolution,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_11339,c_8934,c_8796,c_8933]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_779,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.47/1.49      | sK2 != sK0
% 7.47/1.49      | sK1 != sK1 ),
% 7.47/1.49      inference(resolution_lifted,[status(thm)],[c_34,c_38]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1004,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.47/1.49      | sK2 != sK0 ),
% 7.47/1.49      inference(equality_resolution_simp,[status(thm)],[c_779]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2070,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.47/1.49      | sK2 != sK0
% 7.47/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8793,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.47/1.49      | sK2 != sK0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_8787,c_2070]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8817,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.47/1.49      | sK2 != sK0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_8793,c_8796]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_35,negated_conjecture,
% 7.47/1.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7,plain,
% 7.47/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = X1
% 7.47/1.49      | k1_xboole_0 = X0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_115,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_6,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_116,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1373,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2428,plain,
% 7.47/1.49      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2429,plain,
% 7.47/1.49      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2428]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2427,plain,
% 7.47/1.49      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2715,plain,
% 7.47/1.49      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2427]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1372,plain,( X0 = X0 ),theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2716,plain,
% 7.47/1.49      ( sK0 = sK0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1372]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3470,plain,
% 7.47/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3471,plain,
% 7.47/1.49      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_3470]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_22,plain,
% 7.47/1.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.47/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.47/1.49      | k1_xboole_0 = X0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_578,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK2 != X0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = X0 ),
% 7.47/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_579,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK2 ),
% 7.47/1.49      inference(unflattening,[status(thm)],[c_578]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8,plain,
% 7.47/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_593,plain,
% 7.47/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.47/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK2 ),
% 7.47/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_579,c_8]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2079,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK2
% 7.47/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_599,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK2
% 7.47/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2644,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.47/1.49      | ~ v1_funct_1(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2543]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2645,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.47/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 7.47/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2660,plain,
% 7.47/1.49      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.47/1.49      | k1_xboole_0 = sK2
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_2079,c_40,c_42,c_599,c_2645]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2661,plain,
% 7.47/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK2
% 7.47/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_2660]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8792,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.47/1.49      | sK2 = k1_xboole_0
% 7.47/1.49      | sK1 != k1_xboole_0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_8787,c_2661]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_0,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2411,plain,
% 7.47/1.49      ( ~ r1_tarski(sK2,k1_xboole_0)
% 7.47/1.49      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.47/1.49      | sK2 = k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2588,plain,
% 7.47/1.49      ( sK2 = sK2 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1372]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4,plain,
% 7.47/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4284,plain,
% 7.47/1.49      ( r1_tarski(k1_xboole_0,sK2) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1374,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.47/1.49      theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2568,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1)
% 7.47/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.47/1.49      | sK2 != X0
% 7.47/1.49      | k1_xboole_0 != X1 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_1374]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2942,plain,
% 7.47/1.49      ( ~ r1_tarski(sK2,X0)
% 7.47/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.47/1.49      | sK2 != sK2
% 7.47/1.49      | k1_xboole_0 != X0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2568]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4355,plain,
% 7.47/1.49      ( ~ r1_tarski(sK2,sK0)
% 7.47/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.47/1.49      | sK2 != sK2
% 7.47/1.49      | k1_xboole_0 != sK0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2942]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_9001,plain,
% 7.47/1.49      ( sK2 = k1_xboole_0
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_8792,c_36,c_35,c_115,c_116,c_2411,c_2588,c_3471,c_4284,
% 7.47/1.49                 c_4355,c_7984,c_8810]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_15351,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_8817,c_35,c_115,c_116,c_2429,c_2715,c_2716,c_3471,c_9001,
% 7.47/1.49                 c_11333]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18842,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18820,c_15351]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5,plain,
% 7.47/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_19138,plain,
% 7.47/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.47/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18842,c_5]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18908,plain,
% 7.47/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18820,c_35]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18909,plain,
% 7.47/1.49      ( sK0 = k1_xboole_0 ),
% 7.47/1.49      inference(equality_resolution_simp,[status(thm)],[c_18908]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_19303,plain,
% 7.47/1.49      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18909,c_2083]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2097,plain,
% 7.47/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2100,plain,
% 7.47/1.49      ( X0 = X1
% 7.47/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.47/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5149,plain,
% 7.47/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2097,c_2100]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_19540,plain,
% 7.47/1.49      ( sK2 = k1_xboole_0 ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_19303,c_5149]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18902,plain,
% 7.47/1.49      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18820,c_4082]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_26,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.47/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_694,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.47/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.47/1.49      | sK3 != X0
% 7.47/1.49      | sK1 != X1
% 7.47/1.49      | sK0 != k1_xboole_0 ),
% 7.47/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_695,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.47/1.49      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.47/1.49      | sK0 != k1_xboole_0 ),
% 7.47/1.49      inference(unflattening,[status(thm)],[c_694]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2074,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.47/1.49      | sK0 != k1_xboole_0
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2181,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.47/1.49      | sK0 != k1_xboole_0
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_2074,c_6]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18905,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.47/1.49      | sK0 != k1_xboole_0
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18820,c_2181]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18916,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.47/1.49      | k1_xboole_0 != k1_xboole_0
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(light_normalisation,[status(thm)],[c_18905,c_18909]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18917,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(equality_resolution_simp,[status(thm)],[c_18916]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18907,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18820,c_2082]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18912,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.47/1.49      inference(light_normalisation,[status(thm)],[c_18907,c_18909]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18914,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18912,c_6]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18920,plain,
% 7.47/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.47/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_18917,c_18914]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_18927,plain,
% 7.47/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.47/1.49      inference(light_normalisation,[status(thm)],[c_18902,c_18909,c_18920]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3417,plain,
% 7.47/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_2082,c_2089]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17,plain,
% 7.47/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2091,plain,
% 7.47/1.49      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3438,plain,
% 7.47/1.49      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_3417,c_2091]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_20043,plain,
% 7.47/1.49      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_18927,c_3438]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_22325,plain,
% 7.47/1.49      ( sK3 != sK3 | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(light_normalisation,[status(thm)],[c_19138,c_19540,c_20043]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_22326,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.47/1.49      inference(equality_resolution_simp,[status(thm)],[c_22325]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_22328,plain,
% 7.47/1.49      ( $false ),
% 7.47/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_22326,c_18914]) ).
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  ------                               Statistics
% 7.47/1.49  
% 7.47/1.49  ------ General
% 7.47/1.49  
% 7.47/1.49  abstr_ref_over_cycles:                  0
% 7.47/1.49  abstr_ref_under_cycles:                 0
% 7.47/1.49  gc_basic_clause_elim:                   0
% 7.47/1.49  forced_gc_time:                         0
% 7.47/1.49  parsing_time:                           0.011
% 7.47/1.49  unif_index_cands_time:                  0.
% 7.47/1.49  unif_index_add_time:                    0.
% 7.47/1.49  orderings_time:                         0.
% 7.47/1.49  out_proof_time:                         0.013
% 7.47/1.49  total_time:                             0.536
% 7.47/1.49  num_of_symbols:                         49
% 7.47/1.49  num_of_terms:                           16174
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing
% 7.47/1.49  
% 7.47/1.49  num_of_splits:                          0
% 7.47/1.49  num_of_split_atoms:                     0
% 7.47/1.49  num_of_reused_defs:                     0
% 7.47/1.49  num_eq_ax_congr_red:                    7
% 7.47/1.49  num_of_sem_filtered_clauses:            1
% 7.47/1.49  num_of_subtypes:                        0
% 7.47/1.49  monotx_restored_types:                  0
% 7.47/1.49  sat_num_of_epr_types:                   0
% 7.47/1.49  sat_num_of_non_cyclic_types:            0
% 7.47/1.49  sat_guarded_non_collapsed_types:        0
% 7.47/1.49  num_pure_diseq_elim:                    0
% 7.47/1.49  simp_replaced_by:                       0
% 7.47/1.49  res_preprocessed:                       177
% 7.47/1.49  prep_upred:                             0
% 7.47/1.49  prep_unflattend:                        49
% 7.47/1.49  smt_new_axioms:                         0
% 7.47/1.49  pred_elim_cands:                        4
% 7.47/1.49  pred_elim:                              2
% 7.47/1.49  pred_elim_cl:                           0
% 7.47/1.49  pred_elim_cycles:                       5
% 7.47/1.49  merged_defs:                            8
% 7.47/1.49  merged_defs_ncl:                        0
% 7.47/1.49  bin_hyper_res:                          8
% 7.47/1.49  prep_cycles:                            4
% 7.47/1.49  pred_elim_time:                         0.015
% 7.47/1.49  splitting_time:                         0.
% 7.47/1.49  sem_filter_time:                        0.
% 7.47/1.49  monotx_time:                            0.
% 7.47/1.49  subtype_inf_time:                       0.
% 7.47/1.49  
% 7.47/1.49  ------ Problem properties
% 7.47/1.49  
% 7.47/1.49  clauses:                                38
% 7.47/1.49  conjectures:                            4
% 7.47/1.49  epr:                                    7
% 7.47/1.49  horn:                                   33
% 7.47/1.49  ground:                                 14
% 7.47/1.49  unary:                                  10
% 7.47/1.49  binary:                                 9
% 7.47/1.49  lits:                                   98
% 7.47/1.49  lits_eq:                                38
% 7.47/1.49  fd_pure:                                0
% 7.47/1.49  fd_pseudo:                              0
% 7.47/1.49  fd_cond:                                3
% 7.47/1.49  fd_pseudo_cond:                         1
% 7.47/1.49  ac_symbols:                             0
% 7.47/1.49  
% 7.47/1.49  ------ Propositional Solver
% 7.47/1.49  
% 7.47/1.49  prop_solver_calls:                      28
% 7.47/1.49  prop_fast_solver_calls:                 1680
% 7.47/1.49  smt_solver_calls:                       0
% 7.47/1.49  smt_fast_solver_calls:                  0
% 7.47/1.49  prop_num_of_clauses:                    8159
% 7.47/1.49  prop_preprocess_simplified:             17796
% 7.47/1.49  prop_fo_subsumed:                       46
% 7.47/1.49  prop_solver_time:                       0.
% 7.47/1.49  smt_solver_time:                        0.
% 7.47/1.49  smt_fast_solver_time:                   0.
% 7.47/1.49  prop_fast_solver_time:                  0.
% 7.47/1.49  prop_unsat_core_time:                   0.
% 7.47/1.49  
% 7.47/1.49  ------ QBF
% 7.47/1.49  
% 7.47/1.49  qbf_q_res:                              0
% 7.47/1.49  qbf_num_tautologies:                    0
% 7.47/1.49  qbf_prep_cycles:                        0
% 7.47/1.49  
% 7.47/1.49  ------ BMC1
% 7.47/1.49  
% 7.47/1.49  bmc1_current_bound:                     -1
% 7.47/1.49  bmc1_last_solved_bound:                 -1
% 7.47/1.49  bmc1_unsat_core_size:                   -1
% 7.47/1.49  bmc1_unsat_core_parents_size:           -1
% 7.47/1.49  bmc1_merge_next_fun:                    0
% 7.47/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.47/1.49  
% 7.47/1.49  ------ Instantiation
% 7.47/1.49  
% 7.47/1.49  inst_num_of_clauses:                    2250
% 7.47/1.49  inst_num_in_passive:                    765
% 7.47/1.49  inst_num_in_active:                     929
% 7.47/1.49  inst_num_in_unprocessed:                556
% 7.47/1.49  inst_num_of_loops:                      1170
% 7.47/1.49  inst_num_of_learning_restarts:          0
% 7.47/1.49  inst_num_moves_active_passive:          240
% 7.47/1.49  inst_lit_activity:                      0
% 7.47/1.49  inst_lit_activity_moves:                0
% 7.47/1.49  inst_num_tautologies:                   0
% 7.47/1.49  inst_num_prop_implied:                  0
% 7.47/1.49  inst_num_existing_simplified:           0
% 7.47/1.49  inst_num_eq_res_simplified:             0
% 7.47/1.49  inst_num_child_elim:                    0
% 7.47/1.49  inst_num_of_dismatching_blockings:      800
% 7.47/1.49  inst_num_of_non_proper_insts:           2193
% 7.47/1.49  inst_num_of_duplicates:                 0
% 7.47/1.49  inst_inst_num_from_inst_to_res:         0
% 7.47/1.49  inst_dismatching_checking_time:         0.
% 7.47/1.49  
% 7.47/1.49  ------ Resolution
% 7.47/1.49  
% 7.47/1.49  res_num_of_clauses:                     0
% 7.47/1.49  res_num_in_passive:                     0
% 7.47/1.49  res_num_in_active:                      0
% 7.47/1.49  res_num_of_loops:                       181
% 7.47/1.49  res_forward_subset_subsumed:            83
% 7.47/1.49  res_backward_subset_subsumed:           0
% 7.47/1.49  res_forward_subsumed:                   0
% 7.47/1.49  res_backward_subsumed:                  0
% 7.47/1.49  res_forward_subsumption_resolution:     6
% 7.47/1.49  res_backward_subsumption_resolution:    0
% 7.47/1.49  res_clause_to_clause_subsumption:       2419
% 7.47/1.49  res_orphan_elimination:                 0
% 7.47/1.49  res_tautology_del:                      161
% 7.47/1.49  res_num_eq_res_simplified:              1
% 7.47/1.49  res_num_sel_changes:                    0
% 7.47/1.49  res_moves_from_active_to_pass:          0
% 7.47/1.49  
% 7.47/1.49  ------ Superposition
% 7.47/1.49  
% 7.47/1.49  sup_time_total:                         0.
% 7.47/1.49  sup_time_generating:                    0.
% 7.47/1.49  sup_time_sim_full:                      0.
% 7.47/1.49  sup_time_sim_immed:                     0.
% 7.47/1.49  
% 7.47/1.49  sup_num_of_clauses:                     401
% 7.47/1.49  sup_num_in_active:                      91
% 7.47/1.49  sup_num_in_passive:                     310
% 7.47/1.49  sup_num_of_loops:                       232
% 7.47/1.49  sup_fw_superposition:                   410
% 7.47/1.49  sup_bw_superposition:                   499
% 7.47/1.49  sup_immediate_simplified:               379
% 7.47/1.49  sup_given_eliminated:                   5
% 7.47/1.49  comparisons_done:                       0
% 7.47/1.49  comparisons_avoided:                    50
% 7.47/1.49  
% 7.47/1.49  ------ Simplifications
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  sim_fw_subset_subsumed:                 66
% 7.47/1.49  sim_bw_subset_subsumed:                 50
% 7.47/1.49  sim_fw_subsumed:                        122
% 7.47/1.49  sim_bw_subsumed:                        6
% 7.47/1.49  sim_fw_subsumption_res:                 14
% 7.47/1.49  sim_bw_subsumption_res:                 0
% 7.47/1.49  sim_tautology_del:                      34
% 7.47/1.49  sim_eq_tautology_del:                   97
% 7.47/1.49  sim_eq_res_simp:                        4
% 7.47/1.49  sim_fw_demodulated:                     51
% 7.47/1.49  sim_bw_demodulated:                     148
% 7.47/1.49  sim_light_normalised:                   208
% 7.47/1.49  sim_joinable_taut:                      0
% 7.47/1.49  sim_joinable_simp:                      0
% 7.47/1.49  sim_ac_normalised:                      0
% 7.47/1.49  sim_smt_subsumption:                    0
% 7.47/1.49  
%------------------------------------------------------------------------------
