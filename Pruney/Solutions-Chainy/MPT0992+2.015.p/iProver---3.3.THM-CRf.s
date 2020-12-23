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
% DateTime   : Thu Dec  3 12:03:49 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  205 (8507 expanded)
%              Number of clauses        :  137 (2794 expanded)
%              Number of leaves         :   19 (1589 expanded)
%              Depth                    :   27
%              Number of atoms          :  574 (47098 expanded)
%              Number of equality atoms :  290 (12481 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).

fof(f86,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1960,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_702,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_704,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_35])).

cnf(c_1959,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1965,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3418,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1959,c_1965])).

cnf(c_3564,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_704,c_3418])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1967,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4250,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3564,c_1967])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2264,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2265,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_4599,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4250,c_40,c_2265])).

cnf(c_4600,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4599])).

cnf(c_4609,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1960,c_4600])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4676,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_1961])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1962,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4853,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1962])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_4944,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_37,c_35,c_2434])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1963,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4771,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1963])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2323,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2323])).

cnf(c_2429,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_4936,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4771,c_38,c_40,c_2429])).

cnf(c_4953,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4944,c_4936])).

cnf(c_5857,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4676,c_4953])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_712,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_713,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_424,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_17])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_725,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_713,c_17,c_425])).

cnf(c_1947,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_4951,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4944,c_1947])).

cnf(c_4967,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4951,c_4953])).

cnf(c_6375,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4609,c_4967])).

cnf(c_6837,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5857,c_6375])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5428,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4944,c_1964])).

cnf(c_5741,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5428,c_38,c_40])).

cnf(c_1966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5753,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5741,c_1966])).

cnf(c_1956,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_5752,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5741,c_1956])).

cnf(c_7153,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6837,c_5753,c_5752])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7177,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7153,c_33])).

cnf(c_7178,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7177])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1973,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4225,plain,
    ( sK2 = sK0
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_1973])).

cnf(c_7292,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7178,c_4225])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2293,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1271,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2604,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1272,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3186,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_3187,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3186])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3370,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3368])).

cnf(c_1274,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2460,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_3146,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2460])).

cnf(c_5838,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3146])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5939,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8486,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7292,c_34,c_33,c_105,c_106,c_2293,c_2604,c_3187,c_3370,c_5838,c_5939,c_7153])).

cnf(c_7157,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7153,c_4967])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_7265,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7157,c_5])).

cnf(c_7294,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7178,c_1960])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4249,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1967])).

cnf(c_2253,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2255,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2253])).

cnf(c_2254,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2257,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2254])).

cnf(c_4355,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_2255,c_2257])).

cnf(c_4356,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4355])).

cnf(c_7549,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_7294,c_4356])).

cnf(c_1968,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2807,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1968])).

cnf(c_4227,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2807,c_1973])).

cnf(c_7168,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7153,c_4227])).

cnf(c_7205,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7168,c_7178])).

cnf(c_7208,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7205,c_6])).

cnf(c_2390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2390])).

cnf(c_2393,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_2624,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2627,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2624])).

cnf(c_2696,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2702,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2696])).

cnf(c_2704,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2702])).

cnf(c_3453,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3454,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3453])).

cnf(c_3456,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_7176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7153,c_1959])).

cnf(c_7181,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7176,c_7178])).

cnf(c_7183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7181,c_6])).

cnf(c_8344,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7208,c_2393,c_2627,c_2704,c_3456,c_7183])).

cnf(c_8388,plain,
    ( sK2 != sK2
    | m1_subset_1(k7_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7265,c_7549,c_8344])).

cnf(c_8389,plain,
    ( m1_subset_1(k7_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8388])).

cnf(c_8489,plain,
    ( m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8486,c_8389])).

cnf(c_7161,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7153,c_5741])).

cnf(c_7235,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7161,c_7178])).

cnf(c_7237,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7235,c_6])).

cnf(c_8350,plain,
    ( m1_subset_1(k7_relat_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8344,c_7237])).

cnf(c_8375,plain,
    ( m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8489,c_8375])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:25:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 36
% 3.34/0.98  conjectures                             4
% 3.34/0.98  EPR                                     8
% 3.34/0.98  Horn                                    31
% 3.34/0.98  unary                                   10
% 3.34/0.98  binary                                  7
% 3.34/0.98  lits                                    95
% 3.34/0.98  lits eq                                 37
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 3
% 3.34/0.98  fd_pseudo_cond                          2
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f19,conjecture,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f20,negated_conjecture,(
% 3.34/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.34/0.98    inference(negated_conjecture,[],[f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f40,plain,(
% 3.34/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.34/0.98    inference(ennf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f41,plain,(
% 3.34/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.34/0.98    inference(flattening,[],[f40])).
% 3.34/0.98  
% 3.34/0.98  fof(f49,plain,(
% 3.34/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f50,plain,(
% 3.34/0.98    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).
% 3.34/0.98  
% 3.34/0.98  fof(f86,plain,(
% 3.34/0.98    r1_tarski(sK2,sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f15,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f32,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f15])).
% 3.34/0.98  
% 3.34/0.98  fof(f33,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(flattening,[],[f32])).
% 3.34/0.98  
% 3.34/0.98  fof(f48,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(nnf_transformation,[],[f33])).
% 3.34/0.98  
% 3.34/0.98  fof(f71,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f48])).
% 3.34/0.98  
% 3.34/0.98  fof(f84,plain,(
% 3.34/0.98    v1_funct_2(sK3,sK0,sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f85,plain,(
% 3.34/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f14,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f70,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f31])).
% 3.34/0.98  
% 3.34/0.98  fof(f10,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f26,plain,(
% 3.34/0.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f25])).
% 3.34/0.98  
% 3.34/0.98  fof(f66,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f26])).
% 3.34/0.98  
% 3.34/0.98  fof(f12,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f68,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,axiom,(
% 3.34/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f38,plain,(
% 3.34/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f18])).
% 3.34/0.98  
% 3.34/0.98  fof(f39,plain,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f38])).
% 3.34/0.98  
% 3.34/0.98  fof(f82,plain,(
% 3.34/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f17,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f36,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.34/0.98    inference(ennf_transformation,[],[f17])).
% 3.34/0.98  
% 3.34/0.98  fof(f37,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.34/0.98    inference(flattening,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f79,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f37])).
% 3.34/0.98  
% 3.34/0.98  fof(f83,plain,(
% 3.34/0.98    v1_funct_1(sK3)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f16,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f34,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.34/0.98    inference(ennf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f35,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.34/0.98    inference(flattening,[],[f34])).
% 3.34/0.98  
% 3.34/0.98  fof(f77,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f81,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f88,plain,(
% 3.34/0.98    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f21,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.34/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f30,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f21])).
% 3.34/0.98  
% 3.34/0.98  fof(f69,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f30])).
% 3.34/0.98  
% 3.34/0.98  fof(f8,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f24,plain,(
% 3.34/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f8])).
% 3.34/0.98  
% 3.34/0.98  fof(f47,plain,(
% 3.34/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f24])).
% 3.34/0.98  
% 3.34/0.98  fof(f62,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f47])).
% 3.34/0.98  
% 3.34/0.98  fof(f78,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f87,plain,(
% 3.34/0.98    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f42,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  fof(f43,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(flattening,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f54,plain,(
% 3.34/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f43])).
% 3.34/0.98  
% 3.34/0.98  fof(f4,axiom,(
% 3.34/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f44,plain,(
% 3.34/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.98    inference(nnf_transformation,[],[f4])).
% 3.34/0.98  
% 3.34/0.98  fof(f45,plain,(
% 3.34/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.98    inference(flattening,[],[f44])).
% 3.34/0.98  
% 3.34/0.98  fof(f56,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f45])).
% 3.34/0.98  
% 3.34/0.98  fof(f57,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.34/0.98    inference(cnf_transformation,[],[f45])).
% 3.34/0.98  
% 3.34/0.98  fof(f92,plain,(
% 3.34/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.34/0.98    inference(equality_resolution,[],[f57])).
% 3.34/0.98  
% 3.34/0.98  fof(f6,axiom,(
% 3.34/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f46,plain,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.34/0.98    inference(nnf_transformation,[],[f6])).
% 3.34/0.98  
% 3.34/0.98  fof(f60,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f46])).
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f59,plain,(
% 3.34/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f58,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.34/0.98    inference(cnf_transformation,[],[f45])).
% 3.34/0.98  
% 3.34/0.98  fof(f91,plain,(
% 3.34/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.34/0.98    inference(equality_resolution,[],[f58])).
% 3.34/0.98  
% 3.34/0.98  fof(f9,axiom,(
% 3.34/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f64,plain,(
% 3.34/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.34/0.98    inference(cnf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_34,negated_conjecture,
% 3.34/0.98      ( r1_tarski(sK2,sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1960,plain,
% 3.34/0.98      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_25,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.98      | k1_xboole_0 = X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_36,negated_conjecture,
% 3.34/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_701,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.98      | sK3 != X0
% 3.34/0.98      | sK1 != X2
% 3.34/0.98      | sK0 != X1
% 3.34/0.98      | k1_xboole_0 = X2 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_702,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.34/0.98      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.34/0.98      | k1_xboole_0 = sK1 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_701]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_35,negated_conjecture,
% 3.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_704,plain,
% 3.34/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_702,c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1959,plain,
% 3.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_19,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1965,plain,
% 3.34/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3418,plain,
% 3.34/0.98      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1959,c_1965]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3564,plain,
% 3.34/0.98      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_704,c_3418]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_15,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.34/0.98      | ~ v1_relat_1(X1)
% 3.34/0.98      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1967,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.34/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4250,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.34/0.98      | sK1 = k1_xboole_0
% 3.34/0.98      | r1_tarski(X0,sK0) != iProver_top
% 3.34/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3564,c_1967]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_40,plain,
% 3.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_17,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2264,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.34/0.98      | v1_relat_1(sK3) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2265,plain,
% 3.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.34/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4599,plain,
% 3.34/0.98      ( r1_tarski(X0,sK0) != iProver_top
% 3.34/0.98      | sK1 = k1_xboole_0
% 3.34/0.98      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4250,c_40,c_2265]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4600,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.34/0.98      | sK1 = k1_xboole_0
% 3.34/0.98      | r1_tarski(X0,sK0) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_4599]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4609,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1960,c_4600]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_29,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.34/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1961,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4676,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0
% 3.34/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.34/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.34/0.98      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.34/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4609,c_1961]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_28,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.34/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1962,plain,
% 3.34/0.98      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4853,plain,
% 3.34/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.34/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1959,c_1962]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_37,negated_conjecture,
% 3.34/0.98      ( v1_funct_1(sK3) ),
% 3.34/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2350,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_1(sK3)
% 3.34/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2434,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.34/0.98      | ~ v1_funct_1(sK3)
% 3.34/0.98      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2350]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4944,plain,
% 3.34/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4853,c_37,c_35,c_2434]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_27,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1963,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4771,plain,
% 3.34/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.34/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1959,c_1963]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_38,plain,
% 3.34/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2323,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.34/0.98      | ~ v1_funct_1(sK3) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2428,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.34/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.34/0.98      | ~ v1_funct_1(sK3) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2323]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2429,plain,
% 3.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.34/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4936,plain,
% 3.34/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4771,c_38,c_40,c_2429]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4953,plain,
% 3.34/0.98      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4944,c_4936]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5857,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0
% 3.34/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.34/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.34/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4676,c_4953]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_30,plain,
% 3.34/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.34/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_32,negated_conjecture,
% 3.34/0.98      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.34/0.98      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.34/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_712,plain,
% 3.34/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.34/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.34/0.98      | k1_relat_1(X0) != sK2
% 3.34/0.98      | sK1 != X1 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_713,plain,
% 3.34/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.34/0.98      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.34/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.34/0.98      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.34/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_712]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_18,plain,
% 3.34/0.98      ( v5_relat_1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_12,plain,
% 3.34/0.98      ( ~ v5_relat_1(X0,X1)
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_420,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_424,plain,
% 3.34/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_420,c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_425,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_424]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_725,plain,
% 3.34/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.34/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.34/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_713,c_17,c_425]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1947,plain,
% 3.34/0.98      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.34/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4951,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.34/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.34/0.98      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4944,c_1947]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4967,plain,
% 3.34/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.34/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4951,c_4953]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6375,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0
% 3.34/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4609,c_4967]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6837,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0
% 3.34/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.34/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5857,c_6375]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_26,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1964,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5428,plain,
% 3.34/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.34/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.34/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4944,c_1964]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5741,plain,
% 3.34/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_5428,c_38,c_40]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1966,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5753,plain,
% 3.34/0.98      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5741,c_1966]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1956,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5752,plain,
% 3.34/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5741,c_1956]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7153,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0 ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6837,c_5753,c_5752]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_33,negated_conjecture,
% 3.34/0.98      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7177,plain,
% 3.34/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7153,c_33]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7178,plain,
% 3.34/0.98      ( sK0 = k1_xboole_0 ),
% 3.34/0.98      inference(equality_resolution_simp,[status(thm)],[c_7177]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1973,plain,
% 3.34/0.98      ( X0 = X1
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4225,plain,
% 3.34/0.98      ( sK2 = sK0 | r1_tarski(sK0,sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1960,c_1973]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7292,plain,
% 3.34/0.98      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7178,c_4225]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7,plain,
% 3.34/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = X1
% 3.34/0.98      | k1_xboole_0 = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_105,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_106,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2293,plain,
% 3.34/0.98      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.34/0.98      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.34/0.98      | sK2 = k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1271,plain,( X0 = X0 ),theory(equality) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2604,plain,
% 3.34/0.99      ( sK2 = sK2 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_1271]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1272,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3186,plain,
% 3.34/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_1272]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3187,plain,
% 3.34/0.99      ( sK1 != k1_xboole_0
% 3.34/0.99      | k1_xboole_0 = sK1
% 3.34/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_3186]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_10,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3368,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3370,plain,
% 3.34/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 3.34/0.99      | r1_tarski(k1_xboole_0,sK2) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_3368]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1274,plain,
% 3.34/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.34/0.99      theory(equality) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2460,plain,
% 3.34/0.99      ( ~ r1_tarski(X0,X1)
% 3.34/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.34/0.99      | sK2 != X0
% 3.34/0.99      | k1_xboole_0 != X1 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_1274]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3146,plain,
% 3.34/0.99      ( ~ r1_tarski(sK2,X0)
% 3.34/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.34/0.99      | sK2 != sK2
% 3.34/0.99      | k1_xboole_0 != X0 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_2460]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5838,plain,
% 3.34/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.34/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.34/0.99      | sK2 != sK2
% 3.34/0.99      | k1_xboole_0 != sK0 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_3146]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.34/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5939,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8486,plain,
% 3.34/0.99      ( sK2 = k1_xboole_0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_7292,c_34,c_33,c_105,c_106,c_2293,c_2604,c_3187,
% 3.34/0.99                 c_3370,c_5838,c_5939,c_7153]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7157,plain,
% 3.34/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.34/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7153,c_4967]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5,plain,
% 3.34/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7265,plain,
% 3.34/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.34/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7157,c_5]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7294,plain,
% 3.34/0.99      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7178,c_1960]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_14,plain,
% 3.34/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4249,plain,
% 3.34/0.99      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 3.34/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.34/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_14,c_1967]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2253,plain,
% 3.34/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.99      | v1_relat_1(k1_xboole_0) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2255,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2253]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2254,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2257,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2254]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4355,plain,
% 3.34/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.34/0.99      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_4249,c_2255,c_2257]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4356,plain,
% 3.34/0.99      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 3.34/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_4355]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7549,plain,
% 3.34/0.99      ( k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) = sK2 ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_7294,c_4356]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1968,plain,
% 3.34/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2807,plain,
% 3.34/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1959,c_1968]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4227,plain,
% 3.34/0.99      ( k2_zfmisc_1(sK0,sK1) = sK3
% 3.34/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_2807,c_1973]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7168,plain,
% 3.34/0.99      ( k2_zfmisc_1(sK0,k1_xboole_0) = sK3
% 3.34/0.99      | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) != iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7153,c_4227]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7205,plain,
% 3.34/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
% 3.34/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
% 3.34/0.99      inference(light_normalisation,[status(thm)],[c_7168,c_7178]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7208,plain,
% 3.34/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7205,c_6]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2390,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2391,plain,
% 3.34/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.34/0.99      | r1_tarski(X0,sK3) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2390]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2393,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.34/0.99      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_2391]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2624,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2627,plain,
% 3.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2624]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2696,plain,
% 3.34/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2702,plain,
% 3.34/0.99      ( sK3 = X0
% 3.34/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.34/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2696]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2704,plain,
% 3.34/0.99      ( sK3 = k1_xboole_0
% 3.34/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.34/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_2702]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3453,plain,
% 3.34/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3454,plain,
% 3.34/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.34/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_3453]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3456,plain,
% 3.34/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.34/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_3454]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7176,plain,
% 3.34/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7153,c_1959]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7181,plain,
% 3.34/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.34/0.99      inference(light_normalisation,[status(thm)],[c_7176,c_7178]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7183,plain,
% 3.34/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7181,c_6]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8344,plain,
% 3.34/0.99      ( sK3 = k1_xboole_0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_7208,c_2393,c_2627,c_2704,c_3456,c_7183]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8388,plain,
% 3.34/0.99      ( sK2 != sK2
% 3.34/0.99      | m1_subset_1(k7_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.34/0.99      inference(light_normalisation,[status(thm)],[c_7265,c_7549,c_8344]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8389,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(k1_xboole_0,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.34/0.99      inference(equality_resolution_simp,[status(thm)],[c_8388]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8489,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_8486,c_8389]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7161,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7153,c_5741]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7235,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.34/0.99      inference(light_normalisation,[status(thm)],[c_7161,c_7178]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7237,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7235,c_6]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8350,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_8344,c_7237]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8375,plain,
% 3.34/0.99      ( m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_8350]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(contradiction,plain,
% 3.34/0.99      ( $false ),
% 3.34/0.99      inference(minisat,[status(thm)],[c_8489,c_8375]) ).
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.99  
% 3.34/0.99  ------                               Statistics
% 3.34/0.99  
% 3.34/0.99  ------ General
% 3.34/0.99  
% 3.34/0.99  abstr_ref_over_cycles:                  0
% 3.34/0.99  abstr_ref_under_cycles:                 0
% 3.34/0.99  gc_basic_clause_elim:                   0
% 3.34/0.99  forced_gc_time:                         0
% 3.34/0.99  parsing_time:                           0.01
% 3.34/0.99  unif_index_cands_time:                  0.
% 3.34/0.99  unif_index_add_time:                    0.
% 3.34/0.99  orderings_time:                         0.
% 3.34/0.99  out_proof_time:                         0.015
% 3.34/0.99  total_time:                             0.244
% 3.34/0.99  num_of_symbols:                         50
% 3.34/0.99  num_of_terms:                           6333
% 3.34/0.99  
% 3.34/0.99  ------ Preprocessing
% 3.34/0.99  
% 3.34/0.99  num_of_splits:                          0
% 3.34/0.99  num_of_split_atoms:                     0
% 3.34/0.99  num_of_reused_defs:                     0
% 3.34/0.99  num_eq_ax_congr_red:                    13
% 3.34/0.99  num_of_sem_filtered_clauses:            1
% 3.34/0.99  num_of_subtypes:                        0
% 3.34/0.99  monotx_restored_types:                  0
% 3.34/0.99  sat_num_of_epr_types:                   0
% 3.34/0.99  sat_num_of_non_cyclic_types:            0
% 3.34/0.99  sat_guarded_non_collapsed_types:        0
% 3.34/0.99  num_pure_diseq_elim:                    0
% 3.34/0.99  simp_replaced_by:                       0
% 3.34/0.99  res_preprocessed:                       169
% 3.34/0.99  prep_upred:                             0
% 3.34/0.99  prep_unflattend:                        49
% 3.34/0.99  smt_new_axioms:                         0
% 3.34/0.99  pred_elim_cands:                        5
% 3.34/0.99  pred_elim:                              2
% 3.34/0.99  pred_elim_cl:                           0
% 3.34/0.99  pred_elim_cycles:                       5
% 3.34/0.99  merged_defs:                            8
% 3.34/0.99  merged_defs_ncl:                        0
% 3.34/0.99  bin_hyper_res:                          9
% 3.34/0.99  prep_cycles:                            4
% 3.34/0.99  pred_elim_time:                         0.013
% 3.34/0.99  splitting_time:                         0.
% 3.34/0.99  sem_filter_time:                        0.
% 3.34/0.99  monotx_time:                            0.
% 3.34/0.99  subtype_inf_time:                       0.
% 3.34/0.99  
% 3.34/0.99  ------ Problem properties
% 3.34/0.99  
% 3.34/0.99  clauses:                                36
% 3.34/0.99  conjectures:                            4
% 3.34/0.99  epr:                                    8
% 3.34/0.99  horn:                                   31
% 3.34/0.99  ground:                                 15
% 3.34/0.99  unary:                                  10
% 3.34/0.99  binary:                                 7
% 3.34/0.99  lits:                                   95
% 3.34/0.99  lits_eq:                                37
% 3.34/0.99  fd_pure:                                0
% 3.34/0.99  fd_pseudo:                              0
% 3.34/0.99  fd_cond:                                3
% 3.34/0.99  fd_pseudo_cond:                         2
% 3.34/0.99  ac_symbols:                             0
% 3.34/0.99  
% 3.34/0.99  ------ Propositional Solver
% 3.34/0.99  
% 3.34/0.99  prop_solver_calls:                      30
% 3.34/0.99  prop_fast_solver_calls:                 1328
% 3.34/0.99  smt_solver_calls:                       0
% 3.34/0.99  smt_fast_solver_calls:                  0
% 3.34/0.99  prop_num_of_clauses:                    3002
% 3.34/0.99  prop_preprocess_simplified:             7340
% 3.34/0.99  prop_fo_subsumed:                       26
% 3.34/0.99  prop_solver_time:                       0.
% 3.34/0.99  smt_solver_time:                        0.
% 3.34/0.99  smt_fast_solver_time:                   0.
% 3.34/0.99  prop_fast_solver_time:                  0.
% 3.34/0.99  prop_unsat_core_time:                   0.
% 3.34/0.99  
% 3.34/0.99  ------ QBF
% 3.34/0.99  
% 3.34/0.99  qbf_q_res:                              0
% 3.34/0.99  qbf_num_tautologies:                    0
% 3.34/0.99  qbf_prep_cycles:                        0
% 3.34/0.99  
% 3.34/0.99  ------ BMC1
% 3.34/0.99  
% 3.34/0.99  bmc1_current_bound:                     -1
% 3.34/0.99  bmc1_last_solved_bound:                 -1
% 3.34/0.99  bmc1_unsat_core_size:                   -1
% 3.34/0.99  bmc1_unsat_core_parents_size:           -1
% 3.34/0.99  bmc1_merge_next_fun:                    0
% 3.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.99  
% 3.34/0.99  ------ Instantiation
% 3.34/0.99  
% 3.34/0.99  inst_num_of_clauses:                    845
% 3.34/0.99  inst_num_in_passive:                    417
% 3.34/0.99  inst_num_in_active:                     394
% 3.34/0.99  inst_num_in_unprocessed:                34
% 3.34/0.99  inst_num_of_loops:                      570
% 3.34/0.99  inst_num_of_learning_restarts:          0
% 3.34/0.99  inst_num_moves_active_passive:          172
% 3.34/0.99  inst_lit_activity:                      0
% 3.34/0.99  inst_lit_activity_moves:                0
% 3.34/0.99  inst_num_tautologies:                   0
% 3.34/0.99  inst_num_prop_implied:                  0
% 3.34/0.99  inst_num_existing_simplified:           0
% 3.34/0.99  inst_num_eq_res_simplified:             0
% 3.34/0.99  inst_num_child_elim:                    0
% 3.34/0.99  inst_num_of_dismatching_blockings:      360
% 3.34/0.99  inst_num_of_non_proper_insts:           841
% 3.34/0.99  inst_num_of_duplicates:                 0
% 3.34/0.99  inst_inst_num_from_inst_to_res:         0
% 3.34/0.99  inst_dismatching_checking_time:         0.
% 3.34/0.99  
% 3.34/0.99  ------ Resolution
% 3.34/0.99  
% 3.34/0.99  res_num_of_clauses:                     0
% 3.34/0.99  res_num_in_passive:                     0
% 3.34/0.99  res_num_in_active:                      0
% 3.34/0.99  res_num_of_loops:                       173
% 3.34/0.99  res_forward_subset_subsumed:            51
% 3.34/0.99  res_backward_subset_subsumed:           2
% 3.34/0.99  res_forward_subsumed:                   0
% 3.34/0.99  res_backward_subsumed:                  0
% 3.34/0.99  res_forward_subsumption_resolution:     6
% 3.34/0.99  res_backward_subsumption_resolution:    0
% 3.34/0.99  res_clause_to_clause_subsumption:       634
% 3.34/0.99  res_orphan_elimination:                 0
% 3.34/0.99  res_tautology_del:                      61
% 3.34/0.99  res_num_eq_res_simplified:              1
% 3.34/0.99  res_num_sel_changes:                    0
% 3.34/0.99  res_moves_from_active_to_pass:          0
% 3.34/0.99  
% 3.34/0.99  ------ Superposition
% 3.34/0.99  
% 3.34/0.99  sup_time_total:                         0.
% 3.34/0.99  sup_time_generating:                    0.
% 3.34/0.99  sup_time_sim_full:                      0.
% 3.34/0.99  sup_time_sim_immed:                     0.
% 3.34/0.99  
% 3.34/0.99  sup_num_of_clauses:                     151
% 3.34/0.99  sup_num_in_active:                      52
% 3.34/0.99  sup_num_in_passive:                     99
% 3.34/0.99  sup_num_of_loops:                       112
% 3.34/0.99  sup_fw_superposition:                   105
% 3.34/0.99  sup_bw_superposition:                   106
% 3.34/0.99  sup_immediate_simplified:               55
% 3.34/0.99  sup_given_eliminated:                   0
% 3.34/0.99  comparisons_done:                       0
% 3.34/0.99  comparisons_avoided:                    19
% 3.34/0.99  
% 3.34/0.99  ------ Simplifications
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  sim_fw_subset_subsumed:                 15
% 3.34/0.99  sim_bw_subset_subsumed:                 12
% 3.34/0.99  sim_fw_subsumed:                        10
% 3.34/0.99  sim_bw_subsumed:                        0
% 3.34/0.99  sim_fw_subsumption_res:                 9
% 3.34/0.99  sim_bw_subsumption_res:                 2
% 3.34/0.99  sim_tautology_del:                      7
% 3.34/0.99  sim_eq_tautology_del:                   9
% 3.34/0.99  sim_eq_res_simp:                        4
% 3.34/0.99  sim_fw_demodulated:                     16
% 3.34/0.99  sim_bw_demodulated:                     54
% 3.34/0.99  sim_light_normalised:                   21
% 3.34/0.99  sim_joinable_taut:                      0
% 3.34/0.99  sim_joinable_simp:                      0
% 3.34/0.99  sim_ac_normalised:                      0
% 3.34/0.99  sim_smt_subsumption:                    0
% 3.34/0.99  
%------------------------------------------------------------------------------
