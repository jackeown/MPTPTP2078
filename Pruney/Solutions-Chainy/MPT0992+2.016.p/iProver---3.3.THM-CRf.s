%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:49 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  215 (5821 expanded)
%              Number of clauses        :  139 (1914 expanded)
%              Number of leaves         :   20 (1095 expanded)
%              Depth                    :   27
%              Number of atoms          :  661 (32471 expanded)
%              Number of equality atoms :  331 (8793 expanded)
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

fof(f94,plain,(
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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
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

fof(f78,plain,(
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

fof(f90,plain,(
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

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
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

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,
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

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f102,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f101])).

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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2086,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_771,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_773,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_38])).

cnf(c_2085,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2091,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3980,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2085,c_2091])).

cnf(c_4110,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_773,c_3980])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2094,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5273,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4110,c_2094])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2390,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2391,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2390])).

cnf(c_5797,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5273,c_43,c_2391])).

cnf(c_5798,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5797])).

cnf(c_5808,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2086,c_5798])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5847,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5808,c_2087])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2088,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6031,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2088])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2482,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2578,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_6162,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6031,c_40,c_38,c_2578])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5309,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2089])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2463,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2572,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2463])).

cnf(c_2573,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2572])).

cnf(c_5524,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5309,c_41,c_43,c_2573])).

cnf(c_6171,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6162,c_5524])).

cnf(c_6746,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5847,c_6171])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_781,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_782,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_480,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_19])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_794,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_782,c_19,c_481])).

cnf(c_2072,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_6169,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6162,c_2072])).

cnf(c_6185,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6169,c_6171])).

cnf(c_9844,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5808,c_6185])).

cnf(c_9850,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6746,c_9844])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6908,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6162,c_2090])).

cnf(c_7568,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6908,c_41,c_43])).

cnf(c_2092,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7582,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7568,c_2092])).

cnf(c_2081,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_7580,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7568,c_2081])).

cnf(c_12047,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9850,c_7582,c_7580])).

cnf(c_7578,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_7568,c_2091])).

cnf(c_12075,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_12047,c_7578])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_12099,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12047,c_36])).

cnf(c_12100,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12099])).

cnf(c_12186,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12075,c_12100])).

cnf(c_12080,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12047,c_7568])).

cnf(c_12167,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12080,c_12100])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_12169,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12167,c_6])).

cnf(c_23,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_598,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_599,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_613,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_599,c_8])).

cnf(c_2080,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_619,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_2625,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2624])).

cnf(c_2641,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2080,c_41,c_43,c_619,c_2625])).

cnf(c_2642,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2641])).

cnf(c_6167,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6162,c_2642])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_109,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_117,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_118,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2419,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1379,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2634,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_2636,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_1378,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2441,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_2705,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_1377,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2706,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2592,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2911,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_3337,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_3338,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3337])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4150,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6411,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6167,c_37,c_36,c_109,c_115,c_117,c_118,c_2419,c_2636,c_2705,c_2706,c_2911,c_3338,c_4150,c_5808,c_6185])).

cnf(c_12083,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12047,c_6411])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_12154,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12083,c_5])).

cnf(c_12171,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12169,c_12154])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_696,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_2076,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_2293,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2076,c_6])).

cnf(c_2709,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_41,c_43,c_2625])).

cnf(c_2710,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2709])).

cnf(c_6166,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6162,c_2710])).

cnf(c_6420,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6166,c_6411])).

cnf(c_12082,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12047,c_6420])).

cnf(c_12160,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12082,c_5])).

cnf(c_12172,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12169,c_12160])).

cnf(c_12176,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12171,c_12172])).

cnf(c_12188,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12186,c_12176])).

cnf(c_2098,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5807,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2098,c_5798])).

cnf(c_2493,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2495,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_2765,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8966,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5807,c_38,c_2390,c_2495,c_2765])).

cnf(c_12191,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12188,c_8966])).

cnf(c_12192,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12191])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:05:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options
% 3.62/0.99  
% 3.62/0.99  --out_options                           all
% 3.62/0.99  --tptp_safe_out                         true
% 3.62/0.99  --problem_path                          ""
% 3.62/0.99  --include_path                          ""
% 3.62/0.99  --clausifier                            res/vclausify_rel
% 3.62/0.99  --clausifier_options                    --mode clausify
% 3.62/0.99  --stdin                                 false
% 3.62/0.99  --stats_out                             all
% 3.62/0.99  
% 3.62/0.99  ------ General Options
% 3.62/0.99  
% 3.62/0.99  --fof                                   false
% 3.62/0.99  --time_out_real                         305.
% 3.62/0.99  --time_out_virtual                      -1.
% 3.62/0.99  --symbol_type_check                     false
% 3.62/0.99  --clausify_out                          false
% 3.62/0.99  --sig_cnt_out                           false
% 3.62/0.99  --trig_cnt_out                          false
% 3.62/0.99  --trig_cnt_out_tolerance                1.
% 3.62/0.99  --trig_cnt_out_sk_spl                   false
% 3.62/0.99  --abstr_cl_out                          false
% 3.62/0.99  
% 3.62/0.99  ------ Global Options
% 3.62/0.99  
% 3.62/0.99  --schedule                              default
% 3.62/0.99  --add_important_lit                     false
% 3.62/0.99  --prop_solver_per_cl                    1000
% 3.62/0.99  --min_unsat_core                        false
% 3.62/0.99  --soft_assumptions                      false
% 3.62/0.99  --soft_lemma_size                       3
% 3.62/0.99  --prop_impl_unit_size                   0
% 3.62/0.99  --prop_impl_unit                        []
% 3.62/0.99  --share_sel_clauses                     true
% 3.62/0.99  --reset_solvers                         false
% 3.62/0.99  --bc_imp_inh                            [conj_cone]
% 3.62/0.99  --conj_cone_tolerance                   3.
% 3.62/0.99  --extra_neg_conj                        none
% 3.62/0.99  --large_theory_mode                     true
% 3.62/0.99  --prolific_symb_bound                   200
% 3.62/0.99  --lt_threshold                          2000
% 3.62/0.99  --clause_weak_htbl                      true
% 3.62/0.99  --gc_record_bc_elim                     false
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing Options
% 3.62/0.99  
% 3.62/0.99  --preprocessing_flag                    true
% 3.62/0.99  --time_out_prep_mult                    0.1
% 3.62/0.99  --splitting_mode                        input
% 3.62/0.99  --splitting_grd                         true
% 3.62/0.99  --splitting_cvd                         false
% 3.62/0.99  --splitting_cvd_svl                     false
% 3.62/0.99  --splitting_nvd                         32
% 3.62/0.99  --sub_typing                            true
% 3.62/0.99  --prep_gs_sim                           true
% 3.62/0.99  --prep_unflatten                        true
% 3.62/0.99  --prep_res_sim                          true
% 3.62/0.99  --prep_upred                            true
% 3.62/0.99  --prep_sem_filter                       exhaustive
% 3.62/0.99  --prep_sem_filter_out                   false
% 3.62/0.99  --pred_elim                             true
% 3.62/0.99  --res_sim_input                         true
% 3.62/0.99  --eq_ax_congr_red                       true
% 3.62/0.99  --pure_diseq_elim                       true
% 3.62/0.99  --brand_transform                       false
% 3.62/0.99  --non_eq_to_eq                          false
% 3.62/0.99  --prep_def_merge                        true
% 3.62/0.99  --prep_def_merge_prop_impl              false
% 3.62/0.99  --prep_def_merge_mbd                    true
% 3.62/0.99  --prep_def_merge_tr_red                 false
% 3.62/0.99  --prep_def_merge_tr_cl                  false
% 3.62/0.99  --smt_preprocessing                     true
% 3.62/0.99  --smt_ac_axioms                         fast
% 3.62/0.99  --preprocessed_out                      false
% 3.62/0.99  --preprocessed_stats                    false
% 3.62/0.99  
% 3.62/0.99  ------ Abstraction refinement Options
% 3.62/0.99  
% 3.62/0.99  --abstr_ref                             []
% 3.62/0.99  --abstr_ref_prep                        false
% 3.62/0.99  --abstr_ref_until_sat                   false
% 3.62/0.99  --abstr_ref_sig_restrict                funpre
% 3.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.99  --abstr_ref_under                       []
% 3.62/0.99  
% 3.62/0.99  ------ SAT Options
% 3.62/0.99  
% 3.62/0.99  --sat_mode                              false
% 3.62/0.99  --sat_fm_restart_options                ""
% 3.62/0.99  --sat_gr_def                            false
% 3.62/0.99  --sat_epr_types                         true
% 3.62/0.99  --sat_non_cyclic_types                  false
% 3.62/0.99  --sat_finite_models                     false
% 3.62/0.99  --sat_fm_lemmas                         false
% 3.62/0.99  --sat_fm_prep                           false
% 3.62/0.99  --sat_fm_uc_incr                        true
% 3.62/0.99  --sat_out_model                         small
% 3.62/0.99  --sat_out_clauses                       false
% 3.62/0.99  
% 3.62/0.99  ------ QBF Options
% 3.62/0.99  
% 3.62/0.99  --qbf_mode                              false
% 3.62/0.99  --qbf_elim_univ                         false
% 3.62/0.99  --qbf_dom_inst                          none
% 3.62/0.99  --qbf_dom_pre_inst                      false
% 3.62/0.99  --qbf_sk_in                             false
% 3.62/0.99  --qbf_pred_elim                         true
% 3.62/0.99  --qbf_split                             512
% 3.62/0.99  
% 3.62/0.99  ------ BMC1 Options
% 3.62/0.99  
% 3.62/0.99  --bmc1_incremental                      false
% 3.62/0.99  --bmc1_axioms                           reachable_all
% 3.62/0.99  --bmc1_min_bound                        0
% 3.62/0.99  --bmc1_max_bound                        -1
% 3.62/0.99  --bmc1_max_bound_default                -1
% 3.62/0.99  --bmc1_symbol_reachability              true
% 3.62/0.99  --bmc1_property_lemmas                  false
% 3.62/0.99  --bmc1_k_induction                      false
% 3.62/0.99  --bmc1_non_equiv_states                 false
% 3.62/0.99  --bmc1_deadlock                         false
% 3.62/0.99  --bmc1_ucm                              false
% 3.62/0.99  --bmc1_add_unsat_core                   none
% 3.62/0.99  --bmc1_unsat_core_children              false
% 3.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.99  --bmc1_out_stat                         full
% 3.62/0.99  --bmc1_ground_init                      false
% 3.62/0.99  --bmc1_pre_inst_next_state              false
% 3.62/0.99  --bmc1_pre_inst_state                   false
% 3.62/0.99  --bmc1_pre_inst_reach_state             false
% 3.62/0.99  --bmc1_out_unsat_core                   false
% 3.62/0.99  --bmc1_aig_witness_out                  false
% 3.62/0.99  --bmc1_verbose                          false
% 3.62/0.99  --bmc1_dump_clauses_tptp                false
% 3.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.99  --bmc1_dump_file                        -
% 3.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.99  --bmc1_ucm_extend_mode                  1
% 3.62/0.99  --bmc1_ucm_init_mode                    2
% 3.62/0.99  --bmc1_ucm_cone_mode                    none
% 3.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.99  --bmc1_ucm_relax_model                  4
% 3.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.99  --bmc1_ucm_layered_model                none
% 3.62/0.99  --bmc1_ucm_max_lemma_size               10
% 3.62/0.99  
% 3.62/0.99  ------ AIG Options
% 3.62/0.99  
% 3.62/0.99  --aig_mode                              false
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation Options
% 3.62/0.99  
% 3.62/0.99  --instantiation_flag                    true
% 3.62/0.99  --inst_sos_flag                         false
% 3.62/0.99  --inst_sos_phase                        true
% 3.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel_side                     num_symb
% 3.62/0.99  --inst_solver_per_active                1400
% 3.62/0.99  --inst_solver_calls_frac                1.
% 3.62/0.99  --inst_passive_queue_type               priority_queues
% 3.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.99  --inst_passive_queues_freq              [25;2]
% 3.62/0.99  --inst_dismatching                      true
% 3.62/0.99  --inst_eager_unprocessed_to_passive     true
% 3.62/0.99  --inst_prop_sim_given                   true
% 3.62/0.99  --inst_prop_sim_new                     false
% 3.62/0.99  --inst_subs_new                         false
% 3.62/0.99  --inst_eq_res_simp                      false
% 3.62/0.99  --inst_subs_given                       false
% 3.62/0.99  --inst_orphan_elimination               true
% 3.62/0.99  --inst_learning_loop_flag               true
% 3.62/0.99  --inst_learning_start                   3000
% 3.62/0.99  --inst_learning_factor                  2
% 3.62/0.99  --inst_start_prop_sim_after_learn       3
% 3.62/0.99  --inst_sel_renew                        solver
% 3.62/0.99  --inst_lit_activity_flag                true
% 3.62/0.99  --inst_restr_to_given                   false
% 3.62/0.99  --inst_activity_threshold               500
% 3.62/0.99  --inst_out_proof                        true
% 3.62/0.99  
% 3.62/0.99  ------ Resolution Options
% 3.62/0.99  
% 3.62/0.99  --resolution_flag                       true
% 3.62/0.99  --res_lit_sel                           adaptive
% 3.62/0.99  --res_lit_sel_side                      none
% 3.62/0.99  --res_ordering                          kbo
% 3.62/0.99  --res_to_prop_solver                    active
% 3.62/0.99  --res_prop_simpl_new                    false
% 3.62/0.99  --res_prop_simpl_given                  true
% 3.62/0.99  --res_passive_queue_type                priority_queues
% 3.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.99  --res_passive_queues_freq               [15;5]
% 3.62/0.99  --res_forward_subs                      full
% 3.62/0.99  --res_backward_subs                     full
% 3.62/0.99  --res_forward_subs_resolution           true
% 3.62/0.99  --res_backward_subs_resolution          true
% 3.62/0.99  --res_orphan_elimination                true
% 3.62/0.99  --res_time_limit                        2.
% 3.62/0.99  --res_out_proof                         true
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Options
% 3.62/0.99  
% 3.62/0.99  --superposition_flag                    true
% 3.62/0.99  --sup_passive_queue_type                priority_queues
% 3.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.99  --demod_completeness_check              fast
% 3.62/0.99  --demod_use_ground                      true
% 3.62/0.99  --sup_to_prop_solver                    passive
% 3.62/0.99  --sup_prop_simpl_new                    true
% 3.62/0.99  --sup_prop_simpl_given                  true
% 3.62/0.99  --sup_fun_splitting                     false
% 3.62/0.99  --sup_smt_interval                      50000
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Simplification Setup
% 3.62/0.99  
% 3.62/0.99  --sup_indices_passive                   []
% 3.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_full_bw                           [BwDemod]
% 3.62/0.99  --sup_immed_triv                        [TrivRules]
% 3.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_immed_bw_main                     []
% 3.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.99  
% 3.62/0.99  ------ Combination Options
% 3.62/0.99  
% 3.62/0.99  --comb_res_mult                         3
% 3.62/0.99  --comb_sup_mult                         2
% 3.62/0.99  --comb_inst_mult                        10
% 3.62/0.99  
% 3.62/0.99  ------ Debug Options
% 3.62/0.99  
% 3.62/0.99  --dbg_backtrace                         false
% 3.62/0.99  --dbg_dump_prop_clauses                 false
% 3.62/0.99  --dbg_dump_prop_clauses_file            -
% 3.62/0.99  --dbg_out_stat                          false
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 38
% 3.62/0.99  conjectures                             4
% 3.62/0.99  EPR                                     8
% 3.62/0.99  Horn                                    33
% 3.62/0.99  unary                                   10
% 3.62/0.99  binary                                  9
% 3.62/0.99  lits                                    99
% 3.62/0.99  lits eq                                 37
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 3
% 3.62/0.99  fd_pseudo_cond                          1
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Schedule dynamic 5 is on 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options
% 3.62/0.99  
% 3.62/0.99  --out_options                           all
% 3.62/0.99  --tptp_safe_out                         true
% 3.62/0.99  --problem_path                          ""
% 3.62/0.99  --include_path                          ""
% 3.62/0.99  --clausifier                            res/vclausify_rel
% 3.62/0.99  --clausifier_options                    --mode clausify
% 3.62/0.99  --stdin                                 false
% 3.62/0.99  --stats_out                             all
% 3.62/0.99  
% 3.62/0.99  ------ General Options
% 3.62/0.99  
% 3.62/0.99  --fof                                   false
% 3.62/0.99  --time_out_real                         305.
% 3.62/0.99  --time_out_virtual                      -1.
% 3.62/0.99  --symbol_type_check                     false
% 3.62/0.99  --clausify_out                          false
% 3.62/0.99  --sig_cnt_out                           false
% 3.62/0.99  --trig_cnt_out                          false
% 3.62/0.99  --trig_cnt_out_tolerance                1.
% 3.62/0.99  --trig_cnt_out_sk_spl                   false
% 3.62/0.99  --abstr_cl_out                          false
% 3.62/0.99  
% 3.62/0.99  ------ Global Options
% 3.62/0.99  
% 3.62/0.99  --schedule                              default
% 3.62/0.99  --add_important_lit                     false
% 3.62/0.99  --prop_solver_per_cl                    1000
% 3.62/0.99  --min_unsat_core                        false
% 3.62/0.99  --soft_assumptions                      false
% 3.62/0.99  --soft_lemma_size                       3
% 3.62/0.99  --prop_impl_unit_size                   0
% 3.62/0.99  --prop_impl_unit                        []
% 3.62/0.99  --share_sel_clauses                     true
% 3.62/0.99  --reset_solvers                         false
% 3.62/0.99  --bc_imp_inh                            [conj_cone]
% 3.62/0.99  --conj_cone_tolerance                   3.
% 3.62/0.99  --extra_neg_conj                        none
% 3.62/0.99  --large_theory_mode                     true
% 3.62/0.99  --prolific_symb_bound                   200
% 3.62/0.99  --lt_threshold                          2000
% 3.62/0.99  --clause_weak_htbl                      true
% 3.62/0.99  --gc_record_bc_elim                     false
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing Options
% 3.62/0.99  
% 3.62/0.99  --preprocessing_flag                    true
% 3.62/0.99  --time_out_prep_mult                    0.1
% 3.62/0.99  --splitting_mode                        input
% 3.62/0.99  --splitting_grd                         true
% 3.62/0.99  --splitting_cvd                         false
% 3.62/0.99  --splitting_cvd_svl                     false
% 3.62/0.99  --splitting_nvd                         32
% 3.62/0.99  --sub_typing                            true
% 3.62/0.99  --prep_gs_sim                           true
% 3.62/0.99  --prep_unflatten                        true
% 3.62/0.99  --prep_res_sim                          true
% 3.62/0.99  --prep_upred                            true
% 3.62/0.99  --prep_sem_filter                       exhaustive
% 3.62/0.99  --prep_sem_filter_out                   false
% 3.62/0.99  --pred_elim                             true
% 3.62/0.99  --res_sim_input                         true
% 3.62/0.99  --eq_ax_congr_red                       true
% 3.62/0.99  --pure_diseq_elim                       true
% 3.62/0.99  --brand_transform                       false
% 3.62/0.99  --non_eq_to_eq                          false
% 3.62/0.99  --prep_def_merge                        true
% 3.62/0.99  --prep_def_merge_prop_impl              false
% 3.62/0.99  --prep_def_merge_mbd                    true
% 3.62/0.99  --prep_def_merge_tr_red                 false
% 3.62/0.99  --prep_def_merge_tr_cl                  false
% 3.62/0.99  --smt_preprocessing                     true
% 3.62/0.99  --smt_ac_axioms                         fast
% 3.62/0.99  --preprocessed_out                      false
% 3.62/0.99  --preprocessed_stats                    false
% 3.62/0.99  
% 3.62/0.99  ------ Abstraction refinement Options
% 3.62/0.99  
% 3.62/0.99  --abstr_ref                             []
% 3.62/0.99  --abstr_ref_prep                        false
% 3.62/0.99  --abstr_ref_until_sat                   false
% 3.62/0.99  --abstr_ref_sig_restrict                funpre
% 3.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.99  --abstr_ref_under                       []
% 3.62/0.99  
% 3.62/0.99  ------ SAT Options
% 3.62/0.99  
% 3.62/0.99  --sat_mode                              false
% 3.62/0.99  --sat_fm_restart_options                ""
% 3.62/0.99  --sat_gr_def                            false
% 3.62/0.99  --sat_epr_types                         true
% 3.62/0.99  --sat_non_cyclic_types                  false
% 3.62/0.99  --sat_finite_models                     false
% 3.62/0.99  --sat_fm_lemmas                         false
% 3.62/0.99  --sat_fm_prep                           false
% 3.62/0.99  --sat_fm_uc_incr                        true
% 3.62/0.99  --sat_out_model                         small
% 3.62/0.99  --sat_out_clauses                       false
% 3.62/0.99  
% 3.62/0.99  ------ QBF Options
% 3.62/0.99  
% 3.62/0.99  --qbf_mode                              false
% 3.62/0.99  --qbf_elim_univ                         false
% 3.62/0.99  --qbf_dom_inst                          none
% 3.62/0.99  --qbf_dom_pre_inst                      false
% 3.62/0.99  --qbf_sk_in                             false
% 3.62/0.99  --qbf_pred_elim                         true
% 3.62/0.99  --qbf_split                             512
% 3.62/0.99  
% 3.62/0.99  ------ BMC1 Options
% 3.62/0.99  
% 3.62/0.99  --bmc1_incremental                      false
% 3.62/0.99  --bmc1_axioms                           reachable_all
% 3.62/0.99  --bmc1_min_bound                        0
% 3.62/0.99  --bmc1_max_bound                        -1
% 3.62/0.99  --bmc1_max_bound_default                -1
% 3.62/0.99  --bmc1_symbol_reachability              true
% 3.62/0.99  --bmc1_property_lemmas                  false
% 3.62/0.99  --bmc1_k_induction                      false
% 3.62/0.99  --bmc1_non_equiv_states                 false
% 3.62/0.99  --bmc1_deadlock                         false
% 3.62/0.99  --bmc1_ucm                              false
% 3.62/0.99  --bmc1_add_unsat_core                   none
% 3.62/0.99  --bmc1_unsat_core_children              false
% 3.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.99  --bmc1_out_stat                         full
% 3.62/0.99  --bmc1_ground_init                      false
% 3.62/0.99  --bmc1_pre_inst_next_state              false
% 3.62/0.99  --bmc1_pre_inst_state                   false
% 3.62/0.99  --bmc1_pre_inst_reach_state             false
% 3.62/0.99  --bmc1_out_unsat_core                   false
% 3.62/0.99  --bmc1_aig_witness_out                  false
% 3.62/0.99  --bmc1_verbose                          false
% 3.62/0.99  --bmc1_dump_clauses_tptp                false
% 3.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.99  --bmc1_dump_file                        -
% 3.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.99  --bmc1_ucm_extend_mode                  1
% 3.62/0.99  --bmc1_ucm_init_mode                    2
% 3.62/0.99  --bmc1_ucm_cone_mode                    none
% 3.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.99  --bmc1_ucm_relax_model                  4
% 3.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.99  --bmc1_ucm_layered_model                none
% 3.62/0.99  --bmc1_ucm_max_lemma_size               10
% 3.62/0.99  
% 3.62/0.99  ------ AIG Options
% 3.62/0.99  
% 3.62/0.99  --aig_mode                              false
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation Options
% 3.62/0.99  
% 3.62/0.99  --instantiation_flag                    true
% 3.62/0.99  --inst_sos_flag                         false
% 3.62/0.99  --inst_sos_phase                        true
% 3.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel_side                     none
% 3.62/0.99  --inst_solver_per_active                1400
% 3.62/0.99  --inst_solver_calls_frac                1.
% 3.62/0.99  --inst_passive_queue_type               priority_queues
% 3.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.99  --inst_passive_queues_freq              [25;2]
% 3.62/0.99  --inst_dismatching                      true
% 3.62/0.99  --inst_eager_unprocessed_to_passive     true
% 3.62/0.99  --inst_prop_sim_given                   true
% 3.62/0.99  --inst_prop_sim_new                     false
% 3.62/0.99  --inst_subs_new                         false
% 3.62/0.99  --inst_eq_res_simp                      false
% 3.62/0.99  --inst_subs_given                       false
% 3.62/0.99  --inst_orphan_elimination               true
% 3.62/0.99  --inst_learning_loop_flag               true
% 3.62/0.99  --inst_learning_start                   3000
% 3.62/0.99  --inst_learning_factor                  2
% 3.62/0.99  --inst_start_prop_sim_after_learn       3
% 3.62/0.99  --inst_sel_renew                        solver
% 3.62/0.99  --inst_lit_activity_flag                true
% 3.62/0.99  --inst_restr_to_given                   false
% 3.62/0.99  --inst_activity_threshold               500
% 3.62/0.99  --inst_out_proof                        true
% 3.62/0.99  
% 3.62/0.99  ------ Resolution Options
% 3.62/0.99  
% 3.62/0.99  --resolution_flag                       false
% 3.62/0.99  --res_lit_sel                           adaptive
% 3.62/0.99  --res_lit_sel_side                      none
% 3.62/0.99  --res_ordering                          kbo
% 3.62/0.99  --res_to_prop_solver                    active
% 3.62/0.99  --res_prop_simpl_new                    false
% 3.62/0.99  --res_prop_simpl_given                  true
% 3.62/0.99  --res_passive_queue_type                priority_queues
% 3.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.99  --res_passive_queues_freq               [15;5]
% 3.62/0.99  --res_forward_subs                      full
% 3.62/0.99  --res_backward_subs                     full
% 3.62/0.99  --res_forward_subs_resolution           true
% 3.62/0.99  --res_backward_subs_resolution          true
% 3.62/0.99  --res_orphan_elimination                true
% 3.62/0.99  --res_time_limit                        2.
% 3.62/0.99  --res_out_proof                         true
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Options
% 3.62/0.99  
% 3.62/0.99  --superposition_flag                    true
% 3.62/0.99  --sup_passive_queue_type                priority_queues
% 3.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.99  --demod_completeness_check              fast
% 3.62/0.99  --demod_use_ground                      true
% 3.62/0.99  --sup_to_prop_solver                    passive
% 3.62/0.99  --sup_prop_simpl_new                    true
% 3.62/0.99  --sup_prop_simpl_given                  true
% 3.62/0.99  --sup_fun_splitting                     false
% 3.62/0.99  --sup_smt_interval                      50000
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Simplification Setup
% 3.62/0.99  
% 3.62/0.99  --sup_indices_passive                   []
% 3.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_full_bw                           [BwDemod]
% 3.62/0.99  --sup_immed_triv                        [TrivRules]
% 3.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_immed_bw_main                     []
% 3.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.99  
% 3.62/0.99  ------ Combination Options
% 3.62/0.99  
% 3.62/0.99  --comb_res_mult                         3
% 3.62/0.99  --comb_sup_mult                         2
% 3.62/0.99  --comb_inst_mult                        10
% 3.62/0.99  
% 3.62/0.99  ------ Debug Options
% 3.62/0.99  
% 3.62/0.99  --dbg_backtrace                         false
% 3.62/0.99  --dbg_dump_prop_clauses                 false
% 3.62/0.99  --dbg_dump_prop_clauses_file            -
% 3.62/0.99  --dbg_out_stat                          false
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99   Resolution empty clause
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f21,conjecture,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f22,negated_conjecture,(
% 3.62/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.62/0.99    inference(negated_conjecture,[],[f21])).
% 3.62/0.99  
% 3.62/0.99  fof(f45,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.62/0.99    inference(ennf_transformation,[],[f22])).
% 3.62/0.99  
% 3.62/0.99  fof(f46,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.62/0.99    inference(flattening,[],[f45])).
% 3.62/0.99  
% 3.62/0.99  fof(f54,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f55,plain,(
% 3.62/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f54])).
% 3.62/0.99  
% 3.62/0.99  fof(f94,plain,(
% 3.62/0.99    r1_tarski(sK2,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f17,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f38,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(flattening,[],[f37])).
% 3.62/0.99  
% 3.62/0.99  fof(f53,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(nnf_transformation,[],[f38])).
% 3.62/0.99  
% 3.62/0.99  fof(f79,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f53])).
% 3.62/0.99  
% 3.62/0.99  fof(f92,plain,(
% 3.62/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f93,plain,(
% 3.62/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f36,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f78,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f36])).
% 3.62/0.99  
% 3.62/0.99  fof(f11,axiom,(
% 3.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(flattening,[],[f29])).
% 3.62/0.99  
% 3.62/0.99  fof(f72,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f30])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f75,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f34])).
% 3.62/0.99  
% 3.62/0.99  fof(f20,axiom,(
% 3.62/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f43,plain,(
% 3.62/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.62/0.99    inference(ennf_transformation,[],[f20])).
% 3.62/0.99  
% 3.62/0.99  fof(f44,plain,(
% 3.62/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(flattening,[],[f43])).
% 3.62/0.99  
% 3.62/0.99  fof(f90,plain,(
% 3.62/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f44])).
% 3.62/0.99  
% 3.62/0.99  fof(f19,axiom,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f41,plain,(
% 3.62/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.62/0.99    inference(ennf_transformation,[],[f19])).
% 3.62/0.99  
% 3.62/0.99  fof(f42,plain,(
% 3.62/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.62/0.99    inference(flattening,[],[f41])).
% 3.62/0.99  
% 3.62/0.99  fof(f87,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f42])).
% 3.62/0.99  
% 3.62/0.99  fof(f91,plain,(
% 3.62/0.99    v1_funct_1(sK3)),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f18,axiom,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f39,plain,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.62/0.99    inference(ennf_transformation,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f40,plain,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.62/0.99    inference(flattening,[],[f39])).
% 3.62/0.99  
% 3.62/0.99  fof(f85,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f40])).
% 3.62/0.99  
% 3.62/0.99  fof(f89,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f44])).
% 3.62/0.99  
% 3.62/0.99  fof(f96,plain,(
% 3.62/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f35,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f77,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f35])).
% 3.62/0.99  
% 3.62/0.99  fof(f8,axiom,(
% 3.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f52,plain,(
% 3.62/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(nnf_transformation,[],[f26])).
% 3.62/0.99  
% 3.62/0.99  fof(f67,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f52])).
% 3.62/0.99  
% 3.62/0.99  fof(f86,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f40])).
% 3.62/0.99  
% 3.62/0.99  fof(f95,plain,(
% 3.62/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f49,plain,(
% 3.62/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.62/0.99    inference(nnf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f50,plain,(
% 3.62/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.62/0.99    inference(flattening,[],[f49])).
% 3.62/0.99  
% 3.62/0.99  fof(f62,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f50])).
% 3.62/0.99  
% 3.62/0.99  fof(f100,plain,(
% 3.62/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.62/0.99    inference(equality_resolution,[],[f62])).
% 3.62/0.99  
% 3.62/0.99  fof(f84,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f53])).
% 3.62/0.99  
% 3.62/0.99  fof(f101,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(equality_resolution,[],[f84])).
% 3.62/0.99  
% 3.62/0.99  fof(f102,plain,(
% 3.62/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.62/0.99    inference(equality_resolution,[],[f101])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f64,plain,(
% 3.62/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f6,axiom,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f51,plain,(
% 3.62/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.62/0.99    inference(nnf_transformation,[],[f6])).
% 3.62/0.99  
% 3.62/0.99  fof(f65,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f51])).
% 3.62/0.99  
% 3.62/0.99  fof(f61,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f50])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f47,plain,(
% 3.62/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.99    inference(nnf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f48,plain,(
% 3.62/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.99    inference(flattening,[],[f47])).
% 3.62/0.99  
% 3.62/0.99  fof(f58,plain,(
% 3.62/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.62/0.99    inference(ennf_transformation,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.62/0.99    inference(flattening,[],[f24])).
% 3.62/0.99  
% 3.62/0.99  fof(f59,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f60,plain,(
% 3.62/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f63,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.62/0.99    inference(cnf_transformation,[],[f50])).
% 3.62/0.99  
% 3.62/0.99  fof(f99,plain,(
% 3.62/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.62/0.99    inference(equality_resolution,[],[f63])).
% 3.62/0.99  
% 3.62/0.99  fof(f82,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f53])).
% 3.62/0.99  
% 3.62/0.99  fof(f104,plain,(
% 3.62/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.62/0.99    inference(equality_resolution,[],[f82])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_37,negated_conjecture,
% 3.62/0.99      ( r1_tarski(sK2,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2086,plain,
% 3.62/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_28,plain,
% 3.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.62/0.99      | k1_xboole_0 = X2 ),
% 3.62/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_39,negated_conjecture,
% 3.62/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_770,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.62/0.99      | sK3 != X0
% 3.62/0.99      | sK1 != X2
% 3.62/0.99      | sK0 != X1
% 3.62/0.99      | k1_xboole_0 = X2 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_771,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.62/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.62/0.99      | k1_xboole_0 = sK1 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_770]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_38,negated_conjecture,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_773,plain,
% 3.62/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.62/0.99      inference(global_propositional_subsumption,[status(thm)],[c_771,c_38]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2085,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_22,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2091,plain,
% 3.62/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3980,plain,
% 3.62/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2085,c_2091]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4110,plain,
% 3.62/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_773,c_3980]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_16,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.62/0.99      | ~ v1_relat_1(X1)
% 3.62/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2094,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.62/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5273,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.62/0.99      | sK1 = k1_xboole_0
% 3.62/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4110,c_2094]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_43,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_19,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2390,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.62/0.99      | v1_relat_1(sK3) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2391,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.62/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2390]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5797,plain,
% 3.62/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.62/0.99      | sK1 = k1_xboole_0
% 3.62/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5273,c_43,c_2391]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5798,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.62/0.99      | sK1 = k1_xboole_0
% 3.62/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_5797]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5808,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2086,c_5798]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_32,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.62/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.62/0.99      | ~ v1_funct_1(X0)
% 3.62/0.99      | ~ v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2087,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.62/0.99      | v1_funct_1(X0) != iProver_top
% 3.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5847,plain,
% 3.62/0.99      ( sK1 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.62/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.62/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.62/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5808,c_2087]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_31,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | ~ v1_funct_1(X0)
% 3.62/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.62/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2088,plain,
% 3.62/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.62/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6031,plain,
% 3.62/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.62/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2085,c_2088]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_40,negated_conjecture,
% 3.62/0.99      ( v1_funct_1(sK3) ),
% 3.62/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2482,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.62/0.99      | ~ v1_funct_1(sK3)
% 3.62/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2578,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.62/0.99      | ~ v1_funct_1(sK3)
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2482]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6162,plain,
% 3.62/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6031,c_40,c_38,c_2578]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_30,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | ~ v1_funct_1(X0)
% 3.62/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2089,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/0.99      | v1_funct_1(X0) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5309,plain,
% 3.62/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.62/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2085,c_2089]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_41,plain,
% 3.62/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2463,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.62/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.62/0.99      | ~ v1_funct_1(sK3) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2572,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.62/0.99      | ~ v1_funct_1(sK3) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2463]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2573,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.62/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2572]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5524,plain,
% 3.62/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5309,c_41,c_43,c_2573]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6171,plain,
% 3.62/0.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_6162,c_5524]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6746,plain,
% 3.62/0.99      ( sK1 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.62/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.62/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5847,c_6171]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_33,plain,
% 3.62/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.62/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.62/0.99      | ~ v1_funct_1(X0)
% 3.62/0.99      | ~ v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_35,negated_conjecture,
% 3.62/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.62/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_781,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.62/0.99      | ~ v1_funct_1(X0)
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | ~ v1_relat_1(X0)
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.62/0.99      | k1_relat_1(X0) != sK2
% 3.62/0.99      | sK1 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_782,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_781]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_20,plain,
% 3.62/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12,plain,
% 3.62/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_476,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.62/0.99      | ~ v1_relat_1(X0) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_480,plain,
% 3.62/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.62/0.99      inference(global_propositional_subsumption,[status(thm)],[c_476,c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_481,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_480]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_794,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.62/0.99      inference(forward_subsumption_resolution,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_782,c_19,c_481]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2072,plain,
% 3.62/0.99      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6169,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_6162,c_2072]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6185,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.62/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6169,c_6171]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_9844,plain,
% 3.62/0.99      ( sK1 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5808,c_6185]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_9850,plain,
% 3.62/0.99      ( sK1 = k1_xboole_0
% 3.62/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.62/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6746,c_9844]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_29,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | ~ v1_funct_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2090,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.62/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6908,plain,
% 3.62/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.62/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6162,c_2090]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7568,plain,
% 3.62/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6908,c_41,c_43]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2092,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7582,plain,
% 3.62/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_7568,c_2092]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2081,plain,
% 3.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7580,plain,
% 3.62/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_7568,c_2081]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12047,plain,
% 3.62/0.99      ( sK1 = k1_xboole_0 ),
% 3.62/0.99      inference(forward_subsumption_resolution,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_9850,c_7582,c_7580]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7578,plain,
% 3.62/0.99      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_7568,c_2091]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12075,plain,
% 3.62/0.99      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12047,c_7578]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_36,negated_conjecture,
% 3.62/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12099,plain,
% 3.62/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12047,c_36]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12100,plain,
% 3.62/0.99      ( sK0 = k1_xboole_0 ),
% 3.62/0.99      inference(equality_resolution_simp,[status(thm)],[c_12099]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12186,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_12075,c_12100]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12080,plain,
% 3.62/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12047,c_7568]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12167,plain,
% 3.62/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_12080,c_12100]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12169,plain,
% 3.62/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12167,c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_23,plain,
% 3.62/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.62/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.62/0.99      | k1_xboole_0 = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_598,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK2 != X0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = X0 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_599,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = sK2 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_598]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_8,plain,
% 3.62/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_613,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = sK2 ),
% 3.62/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_599,c_8]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2080,plain,
% 3.62/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = sK2
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_619,plain,
% 3.62/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = sK2
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2624,plain,
% 3.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | ~ v1_funct_1(sK3) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2572]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2625,plain,
% 3.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.62/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2624]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2641,plain,
% 3.62/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | k1_xboole_0 = sK2
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_2080,c_41,c_43,c_619,c_2625]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2642,plain,
% 3.62/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = sK2
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_2641]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6167,plain,
% 3.62/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.62/0.99      | sK2 = k1_xboole_0
% 3.62/0.99      | sK1 != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_6162,c_2642]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_10,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_109,plain,
% 3.62/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.62/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_115,plain,
% 3.62/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7,plain,
% 3.62/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = X1
% 3.62/0.99      | k1_xboole_0 = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_117,plain,
% 3.62/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_118,plain,
% 3.62/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_0,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.62/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2419,plain,
% 3.62/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.62/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.62/0.99      | sK2 = k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1379,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.62/0.99      theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2634,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1)
% 3.62/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.62/0.99      | sK0 != X0
% 3.62/0.99      | k1_xboole_0 != X1 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1379]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2636,plain,
% 3.62/0.99      ( r1_tarski(sK0,k1_xboole_0)
% 3.62/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.62/0.99      | sK0 != k1_xboole_0
% 3.62/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2634]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1378,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2441,plain,
% 3.62/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2705,plain,
% 3.62/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2441]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1377,plain,( X0 = X0 ),theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2706,plain,
% 3.62/0.99      ( sK0 = sK0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1377]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.62/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2592,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.62/0.99      | ~ r1_tarski(sK2,X0)
% 3.62/0.99      | r1_tarski(sK2,k1_xboole_0) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2911,plain,
% 3.62/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.62/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.62/0.99      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2592]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3337,plain,
% 3.62/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3338,plain,
% 3.62/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_3337]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4150,plain,
% 3.62/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6411,plain,
% 3.62/0.99      ( sK2 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6167,c_37,c_36,c_109,c_115,c_117,c_118,c_2419,c_2636,
% 3.62/0.99                 c_2705,c_2706,c_2911,c_3338,c_4150,c_5808,c_6185]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12083,plain,
% 3.62/0.99      ( sK2 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12047,c_6411]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5,plain,
% 3.62/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12154,plain,
% 3.62/0.99      ( sK2 = k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12083,c_5]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12171,plain,
% 3.62/0.99      ( sK2 = k1_xboole_0 ),
% 3.62/0.99      inference(backward_subsumption_resolution,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_12169,c_12154]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_25,plain,
% 3.62/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.62/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_695,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.62/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.62/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | sK1 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_696,plain,
% 3.62/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.62/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.62/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.62/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_695]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2076,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2293,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.62/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_2076,c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2709,plain,
% 3.62/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_2293,c_41,c_43,c_2625]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2710,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_2709]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6166,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | sK2 != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_6162,c_2710]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6420,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6166,c_6411]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12082,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12047,c_6420]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12160,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.62/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12082,c_5]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12172,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.62/0.99      inference(backward_subsumption_resolution,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_12169,c_12160]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12176,plain,
% 3.62/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12171,c_12172]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12188,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_12186,c_12176]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2098,plain,
% 3.62/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5807,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.62/0.99      | sK1 = k1_xboole_0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2098,c_5798]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2493,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.62/0.99      | ~ v1_relat_1(sK3)
% 3.62/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2495,plain,
% 3.62/0.99      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.62/0.99      | ~ v1_relat_1(sK3)
% 3.62/0.99      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_2493]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2765,plain,
% 3.62/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_8966,plain,
% 3.62/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5807,c_38,c_2390,c_2495,c_2765]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12191,plain,
% 3.62/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_12188,c_8966]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_12192,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(equality_resolution_simp,[status(thm)],[c_12191]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ General
% 3.62/0.99  
% 3.62/0.99  abstr_ref_over_cycles:                  0
% 3.62/0.99  abstr_ref_under_cycles:                 0
% 3.62/0.99  gc_basic_clause_elim:                   0
% 3.62/0.99  forced_gc_time:                         0
% 3.62/0.99  parsing_time:                           0.011
% 3.62/0.99  unif_index_cands_time:                  0.
% 3.62/0.99  unif_index_add_time:                    0.
% 3.62/0.99  orderings_time:                         0.
% 3.62/0.99  out_proof_time:                         0.013
% 3.62/0.99  total_time:                             0.295
% 3.62/0.99  num_of_symbols:                         50
% 3.62/0.99  num_of_terms:                           7687
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing
% 3.62/0.99  
% 3.62/0.99  num_of_splits:                          0
% 3.62/0.99  num_of_split_atoms:                     0
% 3.62/0.99  num_of_reused_defs:                     0
% 3.62/0.99  num_eq_ax_congr_red:                    15
% 3.62/0.99  num_of_sem_filtered_clauses:            1
% 3.62/0.99  num_of_subtypes:                        0
% 3.62/0.99  monotx_restored_types:                  0
% 3.62/0.99  sat_num_of_epr_types:                   0
% 3.62/0.99  sat_num_of_non_cyclic_types:            0
% 3.62/0.99  sat_guarded_non_collapsed_types:        0
% 3.62/0.99  num_pure_diseq_elim:                    0
% 3.62/0.99  simp_replaced_by:                       0
% 3.62/0.99  res_preprocessed:                       176
% 3.62/0.99  prep_upred:                             0
% 3.62/0.99  prep_unflattend:                        49
% 3.62/0.99  smt_new_axioms:                         0
% 3.62/0.99  pred_elim_cands:                        4
% 3.62/0.99  pred_elim:                              3
% 3.62/0.99  pred_elim_cl:                           1
% 3.62/0.99  pred_elim_cycles:                       6
% 3.62/0.99  merged_defs:                            8
% 3.62/0.99  merged_defs_ncl:                        0
% 3.62/0.99  bin_hyper_res:                          9
% 3.62/0.99  prep_cycles:                            4
% 3.62/0.99  pred_elim_time:                         0.014
% 3.62/0.99  splitting_time:                         0.
% 3.62/0.99  sem_filter_time:                        0.
% 3.62/0.99  monotx_time:                            0.001
% 3.62/0.99  subtype_inf_time:                       0.
% 3.62/0.99  
% 3.62/0.99  ------ Problem properties
% 3.62/0.99  
% 3.62/0.99  clauses:                                38
% 3.62/0.99  conjectures:                            4
% 3.62/0.99  epr:                                    8
% 3.62/0.99  horn:                                   33
% 3.62/0.99  ground:                                 14
% 3.62/0.99  unary:                                  10
% 3.62/0.99  binary:                                 9
% 3.62/0.99  lits:                                   99
% 3.62/0.99  lits_eq:                                37
% 3.62/0.99  fd_pure:                                0
% 3.62/0.99  fd_pseudo:                              0
% 3.62/0.99  fd_cond:                                3
% 3.62/0.99  fd_pseudo_cond:                         1
% 3.62/0.99  ac_symbols:                             0
% 3.62/0.99  
% 3.62/0.99  ------ Propositional Solver
% 3.62/0.99  
% 3.62/0.99  prop_solver_calls:                      27
% 3.62/0.99  prop_fast_solver_calls:                 1464
% 3.62/0.99  smt_solver_calls:                       0
% 3.62/0.99  smt_fast_solver_calls:                  0
% 3.62/0.99  prop_num_of_clauses:                    4231
% 3.62/0.99  prop_preprocess_simplified:             10851
% 3.62/0.99  prop_fo_subsumed:                       33
% 3.62/0.99  prop_solver_time:                       0.
% 3.62/0.99  smt_solver_time:                        0.
% 3.62/0.99  smt_fast_solver_time:                   0.
% 3.62/0.99  prop_fast_solver_time:                  0.
% 3.62/0.99  prop_unsat_core_time:                   0.
% 3.62/0.99  
% 3.62/0.99  ------ QBF
% 3.62/0.99  
% 3.62/0.99  qbf_q_res:                              0
% 3.62/0.99  qbf_num_tautologies:                    0
% 3.62/0.99  qbf_prep_cycles:                        0
% 3.62/0.99  
% 3.62/0.99  ------ BMC1
% 3.62/0.99  
% 3.62/0.99  bmc1_current_bound:                     -1
% 3.62/0.99  bmc1_last_solved_bound:                 -1
% 3.62/0.99  bmc1_unsat_core_size:                   -1
% 3.62/0.99  bmc1_unsat_core_parents_size:           -1
% 3.62/0.99  bmc1_merge_next_fun:                    0
% 3.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation
% 3.62/0.99  
% 3.62/0.99  inst_num_of_clauses:                    1082
% 3.62/0.99  inst_num_in_passive:                    258
% 3.62/0.99  inst_num_in_active:                     574
% 3.62/0.99  inst_num_in_unprocessed:                250
% 3.62/0.99  inst_num_of_loops:                      730
% 3.62/0.99  inst_num_of_learning_restarts:          0
% 3.62/0.99  inst_num_moves_active_passive:          155
% 3.62/0.99  inst_lit_activity:                      0
% 3.62/0.99  inst_lit_activity_moves:                0
% 3.62/0.99  inst_num_tautologies:                   0
% 3.62/0.99  inst_num_prop_implied:                  0
% 3.62/0.99  inst_num_existing_simplified:           0
% 3.62/0.99  inst_num_eq_res_simplified:             0
% 3.62/0.99  inst_num_child_elim:                    0
% 3.62/0.99  inst_num_of_dismatching_blockings:      413
% 3.62/0.99  inst_num_of_non_proper_insts:           1002
% 3.62/0.99  inst_num_of_duplicates:                 0
% 3.62/0.99  inst_inst_num_from_inst_to_res:         0
% 3.62/0.99  inst_dismatching_checking_time:         0.
% 3.62/0.99  
% 3.62/0.99  ------ Resolution
% 3.62/0.99  
% 3.62/0.99  res_num_of_clauses:                     0
% 3.62/0.99  res_num_in_passive:                     0
% 3.62/0.99  res_num_in_active:                      0
% 3.62/0.99  res_num_of_loops:                       180
% 3.62/0.99  res_forward_subset_subsumed:            52
% 3.62/0.99  res_backward_subset_subsumed:           0
% 3.62/0.99  res_forward_subsumed:                   0
% 3.62/0.99  res_backward_subsumed:                  0
% 3.62/0.99  res_forward_subsumption_resolution:     6
% 3.62/0.99  res_backward_subsumption_resolution:    0
% 3.62/0.99  res_clause_to_clause_subsumption:       1259
% 3.62/0.99  res_orphan_elimination:                 0
% 3.62/0.99  res_tautology_del:                      86
% 3.62/0.99  res_num_eq_res_simplified:              1
% 3.62/0.99  res_num_sel_changes:                    0
% 3.62/0.99  res_moves_from_active_to_pass:          0
% 3.62/0.99  
% 3.62/0.99  ------ Superposition
% 3.62/0.99  
% 3.62/0.99  sup_time_total:                         0.
% 3.62/0.99  sup_time_generating:                    0.
% 3.62/0.99  sup_time_sim_full:                      0.
% 3.62/0.99  sup_time_sim_immed:                     0.
% 3.62/0.99  
% 3.62/0.99  sup_num_of_clauses:                     256
% 3.62/0.99  sup_num_in_active:                      77
% 3.62/0.99  sup_num_in_passive:                     179
% 3.62/0.99  sup_num_of_loops:                       145
% 3.62/0.99  sup_fw_superposition:                   212
% 3.62/0.99  sup_bw_superposition:                   222
% 3.62/0.99  sup_immediate_simplified:               78
% 3.62/0.99  sup_given_eliminated:                   0
% 3.62/0.99  comparisons_done:                       0
% 3.62/0.99  comparisons_avoided:                    34
% 3.62/0.99  
% 3.62/0.99  ------ Simplifications
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  sim_fw_subset_subsumed:                 19
% 3.62/0.99  sim_bw_subset_subsumed:                 16
% 3.62/0.99  sim_fw_subsumed:                        31
% 3.62/0.99  sim_bw_subsumed:                        1
% 3.62/0.99  sim_fw_subsumption_res:                 9
% 3.62/0.99  sim_bw_subsumption_res:                 2
% 3.62/0.99  sim_tautology_del:                      8
% 3.62/0.99  sim_eq_tautology_del:                   19
% 3.62/0.99  sim_eq_res_simp:                        3
% 3.62/0.99  sim_fw_demodulated:                     21
% 3.62/0.99  sim_bw_demodulated:                     62
% 3.62/0.99  sim_light_normalised:                   41
% 3.62/0.99  sim_joinable_taut:                      0
% 3.62/0.99  sim_joinable_simp:                      0
% 3.62/0.99  sim_ac_normalised:                      0
% 3.62/0.99  sim_smt_subsumption:                    0
% 3.62/0.99  
%------------------------------------------------------------------------------
