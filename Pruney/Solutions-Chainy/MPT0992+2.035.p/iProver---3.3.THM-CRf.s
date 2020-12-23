%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:53 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  218 (5279 expanded)
%              Number of clauses        :  143 (1790 expanded)
%              Number of leaves         :   20 ( 965 expanded)
%              Depth                    :   30
%              Number of atoms          :  684 (28757 expanded)
%              Number of equality atoms :  351 (7763 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f52,plain,
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

fof(f53,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f52])).

fof(f91,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1524,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1511,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_629,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_631,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_37])).

cnf(c_1510,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1516,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3163,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1510,c_1516])).

cnf(c_3424,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_631,c_3163])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1522,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5973,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3424,c_1522])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1843,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1844,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_6466,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5973,c_42,c_1844])).

cnf(c_6467,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6466])).

cnf(c_6478,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1511,c_6467])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6947,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_1512])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1517,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3040,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1517])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1519,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4173,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_1519])).

cnf(c_1849,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1850,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1849])).

cnf(c_1942,plain,
    ( ~ v5_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2156,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_2157,plain,
    ( v5_relat_1(sK3,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_4392,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4173,c_42,c_1844,c_1850,c_2157])).

cnf(c_7327,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6947,c_4392])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1513,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7803,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1513])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1925,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3296,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_8714,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7803,c_39,c_37,c_3296])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_639,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_640,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_640,c_19])).

cnf(c_1500,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_8720,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8714,c_1500])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4819,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1514])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1901,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2281,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_2282,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2281])).

cnf(c_5141,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4819,c_40,c_42,c_2282])).

cnf(c_8723,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8714,c_5141])).

cnf(c_8746,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8720,c_8723])).

cnf(c_10639,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_8746])).

cnf(c_10646,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7327,c_10639])).

cnf(c_10897,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10646,c_8723])).

cnf(c_10899,plain,
    ( sK1 = k1_xboole_0
    | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_10897])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8774,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8714,c_1515])).

cnf(c_8886,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8774,c_40,c_42])).

cnf(c_8900,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8886,c_1517])).

cnf(c_26912,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10899,c_4392,c_8900])).

cnf(c_8897,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_8886,c_1516])).

cnf(c_26932,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_26912,c_8897])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26958,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26912,c_35])).

cnf(c_26959,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_26958])).

cnf(c_27027,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_26932,c_26959])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_554,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1504,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1740,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1504,c_5])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_2046,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_2199,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1740,c_40,c_42,c_2046])).

cnf(c_2200,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2199])).

cnf(c_8718,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8714,c_2200])).

cnf(c_26935,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26912,c_8718])).

cnf(c_22,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_455,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_456,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_470,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_456,c_7])).

cnf(c_1508,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_476,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2134,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_40,c_42,c_476,c_2046])).

cnf(c_2135,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2134])).

cnf(c_8719,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8714,c_2135])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_118,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_119,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1867,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_734,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2084,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_735,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2954,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_2955,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(c_3610,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_736,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2067,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_2468,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_3637,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2468])).

cnf(c_9112,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8719,c_36,c_35,c_118,c_119,c_1867,c_2084,c_2444,c_2955,c_3610,c_3637])).

cnf(c_9113,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9112])).

cnf(c_26936,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26912,c_9113])).

cnf(c_27009,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_26936])).

cnf(c_27012,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26935,c_27009])).

cnf(c_27013,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_27012])).

cnf(c_26937,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26912,c_8886])).

cnf(c_27005,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26937,c_26959])).

cnf(c_27007,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27005,c_5])).

cnf(c_27017,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27013,c_27007])).

cnf(c_27018,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27017,c_5])).

cnf(c_27029,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27027,c_27018])).

cnf(c_27033,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27029,c_27007])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1529,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6476,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1529,c_6467])).

cnf(c_1936,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1938,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_2230,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10297,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6476,c_37,c_1843,c_1938,c_2230])).

cnf(c_27034,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27033,c_10297])).

cnf(c_27035,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_27034])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.63/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.49  
% 7.63/1.49  ------  iProver source info
% 7.63/1.49  
% 7.63/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.49  git: non_committed_changes: false
% 7.63/1.49  git: last_make_outside_of_git: false
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options
% 7.63/1.49  
% 7.63/1.49  --out_options                           all
% 7.63/1.49  --tptp_safe_out                         true
% 7.63/1.49  --problem_path                          ""
% 7.63/1.49  --include_path                          ""
% 7.63/1.49  --clausifier                            res/vclausify_rel
% 7.63/1.49  --clausifier_options                    --mode clausify
% 7.63/1.49  --stdin                                 false
% 7.63/1.49  --stats_out                             all
% 7.63/1.49  
% 7.63/1.49  ------ General Options
% 7.63/1.49  
% 7.63/1.49  --fof                                   false
% 7.63/1.49  --time_out_real                         305.
% 7.63/1.49  --time_out_virtual                      -1.
% 7.63/1.49  --symbol_type_check                     false
% 7.63/1.49  --clausify_out                          false
% 7.63/1.49  --sig_cnt_out                           false
% 7.63/1.49  --trig_cnt_out                          false
% 7.63/1.49  --trig_cnt_out_tolerance                1.
% 7.63/1.49  --trig_cnt_out_sk_spl                   false
% 7.63/1.49  --abstr_cl_out                          false
% 7.63/1.49  
% 7.63/1.49  ------ Global Options
% 7.63/1.49  
% 7.63/1.49  --schedule                              default
% 7.63/1.49  --add_important_lit                     false
% 7.63/1.49  --prop_solver_per_cl                    1000
% 7.63/1.49  --min_unsat_core                        false
% 7.63/1.49  --soft_assumptions                      false
% 7.63/1.49  --soft_lemma_size                       3
% 7.63/1.49  --prop_impl_unit_size                   0
% 7.63/1.49  --prop_impl_unit                        []
% 7.63/1.49  --share_sel_clauses                     true
% 7.63/1.49  --reset_solvers                         false
% 7.63/1.49  --bc_imp_inh                            [conj_cone]
% 7.63/1.49  --conj_cone_tolerance                   3.
% 7.63/1.49  --extra_neg_conj                        none
% 7.63/1.49  --large_theory_mode                     true
% 7.63/1.49  --prolific_symb_bound                   200
% 7.63/1.49  --lt_threshold                          2000
% 7.63/1.49  --clause_weak_htbl                      true
% 7.63/1.49  --gc_record_bc_elim                     false
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing Options
% 7.63/1.49  
% 7.63/1.49  --preprocessing_flag                    true
% 7.63/1.49  --time_out_prep_mult                    0.1
% 7.63/1.49  --splitting_mode                        input
% 7.63/1.49  --splitting_grd                         true
% 7.63/1.49  --splitting_cvd                         false
% 7.63/1.49  --splitting_cvd_svl                     false
% 7.63/1.49  --splitting_nvd                         32
% 7.63/1.49  --sub_typing                            true
% 7.63/1.49  --prep_gs_sim                           true
% 7.63/1.49  --prep_unflatten                        true
% 7.63/1.49  --prep_res_sim                          true
% 7.63/1.49  --prep_upred                            true
% 7.63/1.49  --prep_sem_filter                       exhaustive
% 7.63/1.49  --prep_sem_filter_out                   false
% 7.63/1.49  --pred_elim                             true
% 7.63/1.49  --res_sim_input                         true
% 7.63/1.49  --eq_ax_congr_red                       true
% 7.63/1.49  --pure_diseq_elim                       true
% 7.63/1.49  --brand_transform                       false
% 7.63/1.49  --non_eq_to_eq                          false
% 7.63/1.49  --prep_def_merge                        true
% 7.63/1.49  --prep_def_merge_prop_impl              false
% 7.63/1.49  --prep_def_merge_mbd                    true
% 7.63/1.49  --prep_def_merge_tr_red                 false
% 7.63/1.49  --prep_def_merge_tr_cl                  false
% 7.63/1.49  --smt_preprocessing                     true
% 7.63/1.49  --smt_ac_axioms                         fast
% 7.63/1.49  --preprocessed_out                      false
% 7.63/1.49  --preprocessed_stats                    false
% 7.63/1.49  
% 7.63/1.49  ------ Abstraction refinement Options
% 7.63/1.49  
% 7.63/1.49  --abstr_ref                             []
% 7.63/1.49  --abstr_ref_prep                        false
% 7.63/1.49  --abstr_ref_until_sat                   false
% 7.63/1.49  --abstr_ref_sig_restrict                funpre
% 7.63/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.49  --abstr_ref_under                       []
% 7.63/1.49  
% 7.63/1.49  ------ SAT Options
% 7.63/1.49  
% 7.63/1.49  --sat_mode                              false
% 7.63/1.49  --sat_fm_restart_options                ""
% 7.63/1.49  --sat_gr_def                            false
% 7.63/1.49  --sat_epr_types                         true
% 7.63/1.49  --sat_non_cyclic_types                  false
% 7.63/1.49  --sat_finite_models                     false
% 7.63/1.49  --sat_fm_lemmas                         false
% 7.63/1.49  --sat_fm_prep                           false
% 7.63/1.49  --sat_fm_uc_incr                        true
% 7.63/1.49  --sat_out_model                         small
% 7.63/1.49  --sat_out_clauses                       false
% 7.63/1.49  
% 7.63/1.49  ------ QBF Options
% 7.63/1.49  
% 7.63/1.49  --qbf_mode                              false
% 7.63/1.49  --qbf_elim_univ                         false
% 7.63/1.49  --qbf_dom_inst                          none
% 7.63/1.49  --qbf_dom_pre_inst                      false
% 7.63/1.49  --qbf_sk_in                             false
% 7.63/1.49  --qbf_pred_elim                         true
% 7.63/1.49  --qbf_split                             512
% 7.63/1.49  
% 7.63/1.49  ------ BMC1 Options
% 7.63/1.49  
% 7.63/1.49  --bmc1_incremental                      false
% 7.63/1.49  --bmc1_axioms                           reachable_all
% 7.63/1.49  --bmc1_min_bound                        0
% 7.63/1.49  --bmc1_max_bound                        -1
% 7.63/1.49  --bmc1_max_bound_default                -1
% 7.63/1.49  --bmc1_symbol_reachability              true
% 7.63/1.49  --bmc1_property_lemmas                  false
% 7.63/1.49  --bmc1_k_induction                      false
% 7.63/1.49  --bmc1_non_equiv_states                 false
% 7.63/1.49  --bmc1_deadlock                         false
% 7.63/1.49  --bmc1_ucm                              false
% 7.63/1.49  --bmc1_add_unsat_core                   none
% 7.63/1.49  --bmc1_unsat_core_children              false
% 7.63/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.49  --bmc1_out_stat                         full
% 7.63/1.49  --bmc1_ground_init                      false
% 7.63/1.49  --bmc1_pre_inst_next_state              false
% 7.63/1.49  --bmc1_pre_inst_state                   false
% 7.63/1.49  --bmc1_pre_inst_reach_state             false
% 7.63/1.49  --bmc1_out_unsat_core                   false
% 7.63/1.49  --bmc1_aig_witness_out                  false
% 7.63/1.49  --bmc1_verbose                          false
% 7.63/1.49  --bmc1_dump_clauses_tptp                false
% 7.63/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.49  --bmc1_dump_file                        -
% 7.63/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.49  --bmc1_ucm_extend_mode                  1
% 7.63/1.49  --bmc1_ucm_init_mode                    2
% 7.63/1.49  --bmc1_ucm_cone_mode                    none
% 7.63/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.49  --bmc1_ucm_relax_model                  4
% 7.63/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.49  --bmc1_ucm_layered_model                none
% 7.63/1.49  --bmc1_ucm_max_lemma_size               10
% 7.63/1.49  
% 7.63/1.49  ------ AIG Options
% 7.63/1.49  
% 7.63/1.49  --aig_mode                              false
% 7.63/1.49  
% 7.63/1.49  ------ Instantiation Options
% 7.63/1.49  
% 7.63/1.49  --instantiation_flag                    true
% 7.63/1.49  --inst_sos_flag                         false
% 7.63/1.49  --inst_sos_phase                        true
% 7.63/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel_side                     num_symb
% 7.63/1.49  --inst_solver_per_active                1400
% 7.63/1.49  --inst_solver_calls_frac                1.
% 7.63/1.49  --inst_passive_queue_type               priority_queues
% 7.63/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.49  --inst_passive_queues_freq              [25;2]
% 7.63/1.49  --inst_dismatching                      true
% 7.63/1.49  --inst_eager_unprocessed_to_passive     true
% 7.63/1.49  --inst_prop_sim_given                   true
% 7.63/1.49  --inst_prop_sim_new                     false
% 7.63/1.49  --inst_subs_new                         false
% 7.63/1.49  --inst_eq_res_simp                      false
% 7.63/1.49  --inst_subs_given                       false
% 7.63/1.49  --inst_orphan_elimination               true
% 7.63/1.49  --inst_learning_loop_flag               true
% 7.63/1.49  --inst_learning_start                   3000
% 7.63/1.49  --inst_learning_factor                  2
% 7.63/1.49  --inst_start_prop_sim_after_learn       3
% 7.63/1.49  --inst_sel_renew                        solver
% 7.63/1.49  --inst_lit_activity_flag                true
% 7.63/1.49  --inst_restr_to_given                   false
% 7.63/1.49  --inst_activity_threshold               500
% 7.63/1.49  --inst_out_proof                        true
% 7.63/1.49  
% 7.63/1.49  ------ Resolution Options
% 7.63/1.49  
% 7.63/1.49  --resolution_flag                       true
% 7.63/1.49  --res_lit_sel                           adaptive
% 7.63/1.49  --res_lit_sel_side                      none
% 7.63/1.49  --res_ordering                          kbo
% 7.63/1.49  --res_to_prop_solver                    active
% 7.63/1.49  --res_prop_simpl_new                    false
% 7.63/1.49  --res_prop_simpl_given                  true
% 7.63/1.49  --res_passive_queue_type                priority_queues
% 7.63/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.49  --res_passive_queues_freq               [15;5]
% 7.63/1.49  --res_forward_subs                      full
% 7.63/1.49  --res_backward_subs                     full
% 7.63/1.49  --res_forward_subs_resolution           true
% 7.63/1.49  --res_backward_subs_resolution          true
% 7.63/1.49  --res_orphan_elimination                true
% 7.63/1.49  --res_time_limit                        2.
% 7.63/1.49  --res_out_proof                         true
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Options
% 7.63/1.49  
% 7.63/1.49  --superposition_flag                    true
% 7.63/1.49  --sup_passive_queue_type                priority_queues
% 7.63/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.49  --demod_completeness_check              fast
% 7.63/1.49  --demod_use_ground                      true
% 7.63/1.49  --sup_to_prop_solver                    passive
% 7.63/1.49  --sup_prop_simpl_new                    true
% 7.63/1.49  --sup_prop_simpl_given                  true
% 7.63/1.49  --sup_fun_splitting                     false
% 7.63/1.49  --sup_smt_interval                      50000
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Simplification Setup
% 7.63/1.49  
% 7.63/1.49  --sup_indices_passive                   []
% 7.63/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_full_bw                           [BwDemod]
% 7.63/1.49  --sup_immed_triv                        [TrivRules]
% 7.63/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_immed_bw_main                     []
% 7.63/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  
% 7.63/1.49  ------ Combination Options
% 7.63/1.49  
% 7.63/1.49  --comb_res_mult                         3
% 7.63/1.49  --comb_sup_mult                         2
% 7.63/1.49  --comb_inst_mult                        10
% 7.63/1.49  
% 7.63/1.49  ------ Debug Options
% 7.63/1.49  
% 7.63/1.49  --dbg_backtrace                         false
% 7.63/1.49  --dbg_dump_prop_clauses                 false
% 7.63/1.49  --dbg_dump_prop_clauses_file            -
% 7.63/1.49  --dbg_out_stat                          false
% 7.63/1.49  ------ Parsing...
% 7.63/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  ------ Proving...
% 7.63/1.49  ------ Problem Properties 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  clauses                                 40
% 7.63/1.49  conjectures                             4
% 7.63/1.49  EPR                                     6
% 7.63/1.49  Horn                                    35
% 7.63/1.49  unary                                   10
% 7.63/1.49  binary                                  8
% 7.63/1.49  lits                                    108
% 7.63/1.49  lits eq                                 39
% 7.63/1.49  fd_pure                                 0
% 7.63/1.49  fd_pseudo                               0
% 7.63/1.49  fd_cond                                 3
% 7.63/1.49  fd_pseudo_cond                          1
% 7.63/1.49  AC symbols                              0
% 7.63/1.49  
% 7.63/1.49  ------ Schedule dynamic 5 is on 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  Current options:
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options
% 7.63/1.49  
% 7.63/1.49  --out_options                           all
% 7.63/1.49  --tptp_safe_out                         true
% 7.63/1.49  --problem_path                          ""
% 7.63/1.49  --include_path                          ""
% 7.63/1.49  --clausifier                            res/vclausify_rel
% 7.63/1.49  --clausifier_options                    --mode clausify
% 7.63/1.49  --stdin                                 false
% 7.63/1.49  --stats_out                             all
% 7.63/1.49  
% 7.63/1.49  ------ General Options
% 7.63/1.49  
% 7.63/1.49  --fof                                   false
% 7.63/1.49  --time_out_real                         305.
% 7.63/1.49  --time_out_virtual                      -1.
% 7.63/1.49  --symbol_type_check                     false
% 7.63/1.49  --clausify_out                          false
% 7.63/1.49  --sig_cnt_out                           false
% 7.63/1.49  --trig_cnt_out                          false
% 7.63/1.49  --trig_cnt_out_tolerance                1.
% 7.63/1.49  --trig_cnt_out_sk_spl                   false
% 7.63/1.49  --abstr_cl_out                          false
% 7.63/1.49  
% 7.63/1.49  ------ Global Options
% 7.63/1.49  
% 7.63/1.49  --schedule                              default
% 7.63/1.49  --add_important_lit                     false
% 7.63/1.49  --prop_solver_per_cl                    1000
% 7.63/1.49  --min_unsat_core                        false
% 7.63/1.49  --soft_assumptions                      false
% 7.63/1.49  --soft_lemma_size                       3
% 7.63/1.49  --prop_impl_unit_size                   0
% 7.63/1.49  --prop_impl_unit                        []
% 7.63/1.49  --share_sel_clauses                     true
% 7.63/1.49  --reset_solvers                         false
% 7.63/1.49  --bc_imp_inh                            [conj_cone]
% 7.63/1.49  --conj_cone_tolerance                   3.
% 7.63/1.49  --extra_neg_conj                        none
% 7.63/1.49  --large_theory_mode                     true
% 7.63/1.49  --prolific_symb_bound                   200
% 7.63/1.49  --lt_threshold                          2000
% 7.63/1.49  --clause_weak_htbl                      true
% 7.63/1.49  --gc_record_bc_elim                     false
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing Options
% 7.63/1.49  
% 7.63/1.49  --preprocessing_flag                    true
% 7.63/1.49  --time_out_prep_mult                    0.1
% 7.63/1.49  --splitting_mode                        input
% 7.63/1.49  --splitting_grd                         true
% 7.63/1.49  --splitting_cvd                         false
% 7.63/1.49  --splitting_cvd_svl                     false
% 7.63/1.49  --splitting_nvd                         32
% 7.63/1.49  --sub_typing                            true
% 7.63/1.49  --prep_gs_sim                           true
% 7.63/1.49  --prep_unflatten                        true
% 7.63/1.49  --prep_res_sim                          true
% 7.63/1.49  --prep_upred                            true
% 7.63/1.49  --prep_sem_filter                       exhaustive
% 7.63/1.49  --prep_sem_filter_out                   false
% 7.63/1.49  --pred_elim                             true
% 7.63/1.49  --res_sim_input                         true
% 7.63/1.49  --eq_ax_congr_red                       true
% 7.63/1.49  --pure_diseq_elim                       true
% 7.63/1.49  --brand_transform                       false
% 7.63/1.49  --non_eq_to_eq                          false
% 7.63/1.49  --prep_def_merge                        true
% 7.63/1.49  --prep_def_merge_prop_impl              false
% 7.63/1.49  --prep_def_merge_mbd                    true
% 7.63/1.49  --prep_def_merge_tr_red                 false
% 7.63/1.49  --prep_def_merge_tr_cl                  false
% 7.63/1.49  --smt_preprocessing                     true
% 7.63/1.49  --smt_ac_axioms                         fast
% 7.63/1.49  --preprocessed_out                      false
% 7.63/1.49  --preprocessed_stats                    false
% 7.63/1.49  
% 7.63/1.49  ------ Abstraction refinement Options
% 7.63/1.49  
% 7.63/1.49  --abstr_ref                             []
% 7.63/1.49  --abstr_ref_prep                        false
% 7.63/1.49  --abstr_ref_until_sat                   false
% 7.63/1.49  --abstr_ref_sig_restrict                funpre
% 7.63/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.49  --abstr_ref_under                       []
% 7.63/1.49  
% 7.63/1.49  ------ SAT Options
% 7.63/1.49  
% 7.63/1.49  --sat_mode                              false
% 7.63/1.49  --sat_fm_restart_options                ""
% 7.63/1.49  --sat_gr_def                            false
% 7.63/1.49  --sat_epr_types                         true
% 7.63/1.49  --sat_non_cyclic_types                  false
% 7.63/1.49  --sat_finite_models                     false
% 7.63/1.49  --sat_fm_lemmas                         false
% 7.63/1.49  --sat_fm_prep                           false
% 7.63/1.49  --sat_fm_uc_incr                        true
% 7.63/1.49  --sat_out_model                         small
% 7.63/1.49  --sat_out_clauses                       false
% 7.63/1.49  
% 7.63/1.49  ------ QBF Options
% 7.63/1.49  
% 7.63/1.49  --qbf_mode                              false
% 7.63/1.49  --qbf_elim_univ                         false
% 7.63/1.49  --qbf_dom_inst                          none
% 7.63/1.49  --qbf_dom_pre_inst                      false
% 7.63/1.49  --qbf_sk_in                             false
% 7.63/1.49  --qbf_pred_elim                         true
% 7.63/1.49  --qbf_split                             512
% 7.63/1.49  
% 7.63/1.49  ------ BMC1 Options
% 7.63/1.49  
% 7.63/1.49  --bmc1_incremental                      false
% 7.63/1.49  --bmc1_axioms                           reachable_all
% 7.63/1.49  --bmc1_min_bound                        0
% 7.63/1.49  --bmc1_max_bound                        -1
% 7.63/1.49  --bmc1_max_bound_default                -1
% 7.63/1.49  --bmc1_symbol_reachability              true
% 7.63/1.49  --bmc1_property_lemmas                  false
% 7.63/1.49  --bmc1_k_induction                      false
% 7.63/1.49  --bmc1_non_equiv_states                 false
% 7.63/1.49  --bmc1_deadlock                         false
% 7.63/1.49  --bmc1_ucm                              false
% 7.63/1.49  --bmc1_add_unsat_core                   none
% 7.63/1.49  --bmc1_unsat_core_children              false
% 7.63/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.49  --bmc1_out_stat                         full
% 7.63/1.49  --bmc1_ground_init                      false
% 7.63/1.49  --bmc1_pre_inst_next_state              false
% 7.63/1.49  --bmc1_pre_inst_state                   false
% 7.63/1.49  --bmc1_pre_inst_reach_state             false
% 7.63/1.49  --bmc1_out_unsat_core                   false
% 7.63/1.49  --bmc1_aig_witness_out                  false
% 7.63/1.49  --bmc1_verbose                          false
% 7.63/1.49  --bmc1_dump_clauses_tptp                false
% 7.63/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.49  --bmc1_dump_file                        -
% 7.63/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.49  --bmc1_ucm_extend_mode                  1
% 7.63/1.49  --bmc1_ucm_init_mode                    2
% 7.63/1.49  --bmc1_ucm_cone_mode                    none
% 7.63/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.49  --bmc1_ucm_relax_model                  4
% 7.63/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.49  --bmc1_ucm_layered_model                none
% 7.63/1.49  --bmc1_ucm_max_lemma_size               10
% 7.63/1.49  
% 7.63/1.49  ------ AIG Options
% 7.63/1.49  
% 7.63/1.49  --aig_mode                              false
% 7.63/1.49  
% 7.63/1.49  ------ Instantiation Options
% 7.63/1.49  
% 7.63/1.49  --instantiation_flag                    true
% 7.63/1.49  --inst_sos_flag                         false
% 7.63/1.49  --inst_sos_phase                        true
% 7.63/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel_side                     none
% 7.63/1.49  --inst_solver_per_active                1400
% 7.63/1.49  --inst_solver_calls_frac                1.
% 7.63/1.49  --inst_passive_queue_type               priority_queues
% 7.63/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.49  --inst_passive_queues_freq              [25;2]
% 7.63/1.49  --inst_dismatching                      true
% 7.63/1.49  --inst_eager_unprocessed_to_passive     true
% 7.63/1.49  --inst_prop_sim_given                   true
% 7.63/1.49  --inst_prop_sim_new                     false
% 7.63/1.49  --inst_subs_new                         false
% 7.63/1.49  --inst_eq_res_simp                      false
% 7.63/1.49  --inst_subs_given                       false
% 7.63/1.49  --inst_orphan_elimination               true
% 7.63/1.49  --inst_learning_loop_flag               true
% 7.63/1.49  --inst_learning_start                   3000
% 7.63/1.49  --inst_learning_factor                  2
% 7.63/1.49  --inst_start_prop_sim_after_learn       3
% 7.63/1.49  --inst_sel_renew                        solver
% 7.63/1.49  --inst_lit_activity_flag                true
% 7.63/1.49  --inst_restr_to_given                   false
% 7.63/1.49  --inst_activity_threshold               500
% 7.63/1.49  --inst_out_proof                        true
% 7.63/1.49  
% 7.63/1.49  ------ Resolution Options
% 7.63/1.49  
% 7.63/1.49  --resolution_flag                       false
% 7.63/1.49  --res_lit_sel                           adaptive
% 7.63/1.49  --res_lit_sel_side                      none
% 7.63/1.49  --res_ordering                          kbo
% 7.63/1.49  --res_to_prop_solver                    active
% 7.63/1.49  --res_prop_simpl_new                    false
% 7.63/1.49  --res_prop_simpl_given                  true
% 7.63/1.49  --res_passive_queue_type                priority_queues
% 7.63/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.49  --res_passive_queues_freq               [15;5]
% 7.63/1.49  --res_forward_subs                      full
% 7.63/1.49  --res_backward_subs                     full
% 7.63/1.49  --res_forward_subs_resolution           true
% 7.63/1.49  --res_backward_subs_resolution          true
% 7.63/1.49  --res_orphan_elimination                true
% 7.63/1.49  --res_time_limit                        2.
% 7.63/1.49  --res_out_proof                         true
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Options
% 7.63/1.49  
% 7.63/1.49  --superposition_flag                    true
% 7.63/1.49  --sup_passive_queue_type                priority_queues
% 7.63/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.49  --demod_completeness_check              fast
% 7.63/1.49  --demod_use_ground                      true
% 7.63/1.49  --sup_to_prop_solver                    passive
% 7.63/1.49  --sup_prop_simpl_new                    true
% 7.63/1.49  --sup_prop_simpl_given                  true
% 7.63/1.49  --sup_fun_splitting                     false
% 7.63/1.49  --sup_smt_interval                      50000
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Simplification Setup
% 7.63/1.49  
% 7.63/1.49  --sup_indices_passive                   []
% 7.63/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_full_bw                           [BwDemod]
% 7.63/1.49  --sup_immed_triv                        [TrivRules]
% 7.63/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_immed_bw_main                     []
% 7.63/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  
% 7.63/1.49  ------ Combination Options
% 7.63/1.49  
% 7.63/1.49  --comb_res_mult                         3
% 7.63/1.49  --comb_sup_mult                         2
% 7.63/1.49  --comb_inst_mult                        10
% 7.63/1.49  
% 7.63/1.49  ------ Debug Options
% 7.63/1.49  
% 7.63/1.49  --dbg_backtrace                         false
% 7.63/1.49  --dbg_dump_prop_clauses                 false
% 7.63/1.49  --dbg_dump_prop_clauses_file            -
% 7.63/1.49  --dbg_out_stat                          false
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS status Theorem for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49   Resolution empty clause
% 7.63/1.49  
% 7.63/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  fof(f7,axiom,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f24,plain,(
% 7.63/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f7])).
% 7.63/1.49  
% 7.63/1.49  fof(f50,plain,(
% 7.63/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(nnf_transformation,[],[f24])).
% 7.63/1.49  
% 7.63/1.49  fof(f64,plain,(
% 7.63/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f50])).
% 7.63/1.49  
% 7.63/1.49  fof(f20,conjecture,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f21,negated_conjecture,(
% 7.63/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.63/1.49    inference(negated_conjecture,[],[f20])).
% 7.63/1.49  
% 7.63/1.49  fof(f43,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.63/1.49    inference(ennf_transformation,[],[f21])).
% 7.63/1.49  
% 7.63/1.49  fof(f44,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.63/1.49    inference(flattening,[],[f43])).
% 7.63/1.49  
% 7.63/1.49  fof(f52,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f53,plain,(
% 7.63/1.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f52])).
% 7.63/1.49  
% 7.63/1.49  fof(f91,plain,(
% 7.63/1.49    r1_tarski(sK2,sK0)),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f16,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f35,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f16])).
% 7.63/1.49  
% 7.63/1.49  fof(f36,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(flattening,[],[f35])).
% 7.63/1.49  
% 7.63/1.49  fof(f51,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(nnf_transformation,[],[f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f76,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f51])).
% 7.63/1.49  
% 7.63/1.49  fof(f89,plain,(
% 7.63/1.49    v1_funct_2(sK3,sK0,sK1)),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f90,plain,(
% 7.63/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f15,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f34,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f15])).
% 7.63/1.49  
% 7.63/1.49  fof(f75,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f34])).
% 7.63/1.49  
% 7.63/1.49  fof(f10,axiom,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f27,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f10])).
% 7.63/1.49  
% 7.63/1.49  fof(f28,plain,(
% 7.63/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(flattening,[],[f27])).
% 7.63/1.49  
% 7.63/1.49  fof(f69,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f28])).
% 7.63/1.49  
% 7.63/1.49  fof(f13,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f32,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f73,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f32])).
% 7.63/1.49  
% 7.63/1.49  fof(f19,axiom,(
% 7.63/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f41,plain,(
% 7.63/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.63/1.49    inference(ennf_transformation,[],[f19])).
% 7.63/1.49  
% 7.63/1.49  fof(f42,plain,(
% 7.63/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(flattening,[],[f41])).
% 7.63/1.49  
% 7.63/1.49  fof(f87,plain,(
% 7.63/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f42])).
% 7.63/1.49  
% 7.63/1.49  fof(f14,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f22,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.63/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.63/1.49  
% 7.63/1.49  fof(f33,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f74,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f33])).
% 7.63/1.49  
% 7.63/1.49  fof(f12,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f30,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 7.63/1.49    inference(ennf_transformation,[],[f12])).
% 7.63/1.49  
% 7.63/1.49  fof(f31,plain,(
% 7.63/1.49    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 7.63/1.49    inference(flattening,[],[f30])).
% 7.63/1.49  
% 7.63/1.49  fof(f71,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f31])).
% 7.63/1.49  
% 7.63/1.49  fof(f18,axiom,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f39,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.63/1.49    inference(ennf_transformation,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f40,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.63/1.49    inference(flattening,[],[f39])).
% 7.63/1.49  
% 7.63/1.49  fof(f84,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f40])).
% 7.63/1.49  
% 7.63/1.49  fof(f88,plain,(
% 7.63/1.49    v1_funct_1(sK3)),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f86,plain,(
% 7.63/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f42])).
% 7.63/1.49  
% 7.63/1.49  fof(f93,plain,(
% 7.63/1.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f17,axiom,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f37,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.63/1.49    inference(ennf_transformation,[],[f17])).
% 7.63/1.49  
% 7.63/1.49  fof(f38,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.63/1.49    inference(flattening,[],[f37])).
% 7.63/1.49  
% 7.63/1.49  fof(f82,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f38])).
% 7.63/1.49  
% 7.63/1.49  fof(f83,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f38])).
% 7.63/1.49  
% 7.63/1.49  fof(f92,plain,(
% 7.63/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.63/1.49    inference(cnf_transformation,[],[f53])).
% 7.63/1.49  
% 7.63/1.49  fof(f79,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f51])).
% 7.63/1.49  
% 7.63/1.49  fof(f101,plain,(
% 7.63/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.63/1.49    inference(equality_resolution,[],[f79])).
% 7.63/1.49  
% 7.63/1.49  fof(f3,axiom,(
% 7.63/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f47,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.63/1.49    inference(nnf_transformation,[],[f3])).
% 7.63/1.49  
% 7.63/1.49  fof(f48,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.63/1.49    inference(flattening,[],[f47])).
% 7.63/1.49  
% 7.63/1.49  fof(f59,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.63/1.49    inference(cnf_transformation,[],[f48])).
% 7.63/1.49  
% 7.63/1.49  fof(f97,plain,(
% 7.63/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.63/1.49    inference(equality_resolution,[],[f59])).
% 7.63/1.49  
% 7.63/1.49  fof(f81,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f51])).
% 7.63/1.49  
% 7.63/1.49  fof(f98,plain,(
% 7.63/1.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(equality_resolution,[],[f81])).
% 7.63/1.49  
% 7.63/1.49  fof(f99,plain,(
% 7.63/1.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.63/1.49    inference(equality_resolution,[],[f98])).
% 7.63/1.49  
% 7.63/1.49  fof(f4,axiom,(
% 7.63/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f61,plain,(
% 7.63/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f4])).
% 7.63/1.49  
% 7.63/1.49  fof(f58,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f48])).
% 7.63/1.49  
% 7.63/1.49  fof(f1,axiom,(
% 7.63/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f45,plain,(
% 7.63/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.49    inference(nnf_transformation,[],[f1])).
% 7.63/1.49  
% 7.63/1.49  fof(f46,plain,(
% 7.63/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.49    inference(flattening,[],[f45])).
% 7.63/1.49  
% 7.63/1.49  fof(f56,plain,(
% 7.63/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f46])).
% 7.63/1.49  
% 7.63/1.49  fof(f5,axiom,(
% 7.63/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f49,plain,(
% 7.63/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.63/1.49    inference(nnf_transformation,[],[f5])).
% 7.63/1.49  
% 7.63/1.49  fof(f62,plain,(
% 7.63/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f49])).
% 7.63/1.49  
% 7.63/1.49  fof(f2,axiom,(
% 7.63/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f57,plain,(
% 7.63/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f2])).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11,plain,
% 7.63/1.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1524,plain,
% 7.63/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 7.63/1.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.63/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_36,negated_conjecture,
% 7.63/1.49      ( r1_tarski(sK2,sK0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1511,plain,
% 7.63/1.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_27,plain,
% 7.63/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.63/1.50      | k1_xboole_0 = X2 ),
% 7.63/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_38,negated_conjecture,
% 7.63/1.50      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_628,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.63/1.50      | sK3 != X0
% 7.63/1.50      | sK1 != X2
% 7.63/1.50      | sK0 != X1
% 7.63/1.50      | k1_xboole_0 = X2 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_629,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.63/1.50      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.63/1.50      | k1_xboole_0 = sK1 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_628]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_37,negated_conjecture,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.63/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_631,plain,
% 7.63/1.50      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.63/1.50      inference(global_propositional_subsumption,[status(thm)],[c_629,c_37]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1510,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1516,plain,
% 7.63/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.63/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3163,plain,
% 7.63/1.50      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1510,c_1516]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3424,plain,
% 7.63/1.50      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_631,c_3163]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.63/1.50      | ~ v1_relat_1(X1)
% 7.63/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1522,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.63/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.63/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5973,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.63/1.50      | sK1 = k1_xboole_0
% 7.63/1.50      | r1_tarski(X0,sK0) != iProver_top
% 7.63/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3424,c_1522]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_42,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_19,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1843,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.63/1.50      | v1_relat_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1844,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.63/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6466,plain,
% 7.63/1.50      ( r1_tarski(X0,sK0) != iProver_top
% 7.63/1.50      | sK1 = k1_xboole_0
% 7.63/1.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_5973,c_42,c_1844]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6467,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.63/1.50      | sK1 = k1_xboole_0
% 7.63/1.50      | r1_tarski(X0,sK0) != iProver_top ),
% 7.63/1.50      inference(renaming,[status(thm)],[c_6466]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6478,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1511,c_6467]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_31,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.63/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.63/1.50      | ~ v1_funct_1(X0)
% 7.63/1.50      | ~ v1_relat_1(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1512,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.63/1.50      | v1_funct_1(X0) != iProver_top
% 7.63/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6947,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.63/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.63/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_6478,c_1512]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_20,plain,
% 7.63/1.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.63/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1517,plain,
% 7.63/1.50      ( v5_relat_1(X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3040,plain,
% 7.63/1.50      ( v5_relat_1(sK3,sK1) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1510,c_1517]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_18,plain,
% 7.63/1.50      ( ~ v5_relat_1(X0,X1)
% 7.63/1.50      | ~ v1_relat_1(X0)
% 7.63/1.50      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1519,plain,
% 7.63/1.50      ( v5_relat_1(X0,X1) != iProver_top
% 7.63/1.50      | v1_relat_1(X0) != iProver_top
% 7.63/1.50      | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4173,plain,
% 7.63/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.63/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3040,c_1519]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1849,plain,
% 7.63/1.50      ( v5_relat_1(sK3,sK1)
% 7.63/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1850,plain,
% 7.63/1.50      ( v5_relat_1(sK3,sK1) = iProver_top
% 7.63/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1849]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1942,plain,
% 7.63/1.50      ( ~ v5_relat_1(sK3,X0)
% 7.63/1.50      | v1_relat_1(k7_relat_1(sK3,X1))
% 7.63/1.50      | ~ v1_relat_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2156,plain,
% 7.63/1.50      ( ~ v5_relat_1(sK3,sK1)
% 7.63/1.50      | v1_relat_1(k7_relat_1(sK3,X0))
% 7.63/1.50      | ~ v1_relat_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1942]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2157,plain,
% 7.63/1.50      ( v5_relat_1(sK3,sK1) != iProver_top
% 7.63/1.50      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.63/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4392,plain,
% 7.63/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_4173,c_42,c_1844,c_1850,c_2157]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7327,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.63/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_6947,c_4392]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_30,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | ~ v1_funct_1(X0)
% 7.63/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.63/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1513,plain,
% 7.63/1.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.63/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.63/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7803,plain,
% 7.63/1.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.63/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1510,c_1513]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_39,negated_conjecture,
% 7.63/1.50      ( v1_funct_1(sK3) ),
% 7.63/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1925,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.63/1.50      | ~ v1_funct_1(sK3)
% 7.63/1.50      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_30]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3296,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.63/1.50      | ~ v1_funct_1(sK3)
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1925]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8714,plain,
% 7.63/1.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_7803,c_39,c_37,c_3296]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_32,plain,
% 7.63/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.63/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.63/1.50      | ~ v1_funct_1(X0)
% 7.63/1.50      | ~ v1_relat_1(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_34,negated_conjecture,
% 7.63/1.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.63/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_639,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.63/1.50      | ~ v1_funct_1(X0)
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | ~ v1_relat_1(X0)
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.63/1.50      | k1_relat_1(X0) != sK2
% 7.63/1.50      | sK1 != X1 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_640,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_639]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_652,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_640,c_19]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1500,plain,
% 7.63/1.50      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8720,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.63/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_8714,c_1500]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_29,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | ~ v1_funct_1(X0)
% 7.63/1.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1514,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.63/1.50      | v1_funct_1(X0) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4819,plain,
% 7.63/1.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.63/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1510,c_1514]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_40,plain,
% 7.63/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1901,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.63/1.50      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 7.63/1.50      | ~ v1_funct_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2281,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 7.63/1.50      | ~ v1_funct_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1901]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2282,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.63/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2281]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5141,plain,
% 7.63/1.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_4819,c_40,c_42,c_2282]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8723,plain,
% 7.63/1.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_8714,c_5141]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8746,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_8720,c_8723]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10639,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_6478,c_8746]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10646,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.63/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_7327,c_10639]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10897,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_10646,c_8723]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10899,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0
% 7.63/1.50      | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
% 7.63/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1524,c_10897]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_28,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.50      | ~ v1_funct_1(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1515,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.63/1.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.63/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8774,plain,
% 7.63/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.63/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8714,c_1515]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8886,plain,
% 7.63/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_8774,c_40,c_42]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8900,plain,
% 7.63/1.50      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8886,c_1517]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26912,plain,
% 7.63/1.50      ( sK1 = k1_xboole_0 ),
% 7.63/1.50      inference(forward_subsumption_resolution,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_10899,c_4392,c_8900]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8897,plain,
% 7.63/1.50      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8886,c_1516]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26932,plain,
% 7.63/1.50      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_26912,c_8897]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_35,negated_conjecture,
% 7.63/1.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26958,plain,
% 7.63/1.50      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_26912,c_35]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26959,plain,
% 7.63/1.50      ( sK0 = k1_xboole_0 ),
% 7.63/1.50      inference(equality_resolution_simp,[status(thm)],[c_26958]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27027,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_26932,c_26959]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_24,plain,
% 7.63/1.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.63/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_553,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.63/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.63/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | sK1 != X1 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_554,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_553]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1504,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5,plain,
% 7.63/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1740,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1504,c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2045,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | ~ v1_funct_1(sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1901]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2046,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 7.63/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2199,plain,
% 7.63/1.50      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_1740,c_40,c_42,c_2046]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2200,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(renaming,[status(thm)],[c_2199]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8718,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_8714,c_2200]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26935,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 7.63/1.50      | sK2 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_26912,c_8718]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22,plain,
% 7.63/1.50      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.63/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_455,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK2 != X0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_456,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK2 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_455]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_470,plain,
% 7.63/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.63/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK2 ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_456,c_7]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1508,plain,
% 7.63/1.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK2
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_476,plain,
% 7.63/1.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK2
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2134,plain,
% 7.63/1.50      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.63/1.50      | k1_xboole_0 = sK2
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_1508,c_40,c_42,c_476,c_2046]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2135,plain,
% 7.63/1.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK2
% 7.63/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.63/1.50      inference(renaming,[status(thm)],[c_2134]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8719,plain,
% 7.63/1.50      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.63/1.50      | sK2 = k1_xboole_0
% 7.63/1.50      | sK1 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_8714,c_2135]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6,plain,
% 7.63/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = X1
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_118,plain,
% 7.63/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_119,plain,
% 7.63/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_0,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.63/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1867,plain,
% 7.63/1.50      ( ~ r1_tarski(sK2,k1_xboole_0)
% 7.63/1.50      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.63/1.50      | sK2 = k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_734,plain,( X0 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2084,plain,
% 7.63/1.50      ( sK2 = sK2 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_734]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2442,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2444,plain,
% 7.63/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 7.63/1.50      | r1_tarski(k1_xboole_0,sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2442]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_735,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2954,plain,
% 7.63/1.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_735]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2955,plain,
% 7.63/1.50      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2954]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3610,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_736,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.63/1.50      theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2067,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,X1)
% 7.63/1.50      | r1_tarski(sK2,k1_xboole_0)
% 7.63/1.50      | sK2 != X0
% 7.63/1.50      | k1_xboole_0 != X1 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_736]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2468,plain,
% 7.63/1.50      ( ~ r1_tarski(sK2,X0)
% 7.63/1.50      | r1_tarski(sK2,k1_xboole_0)
% 7.63/1.50      | sK2 != sK2
% 7.63/1.50      | k1_xboole_0 != X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2067]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3637,plain,
% 7.63/1.50      ( ~ r1_tarski(sK2,sK0)
% 7.63/1.50      | r1_tarski(sK2,k1_xboole_0)
% 7.63/1.50      | sK2 != sK2
% 7.63/1.50      | k1_xboole_0 != sK0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2468]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9112,plain,
% 7.63/1.50      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_8719,c_36,c_35,c_118,c_119,c_1867,c_2084,c_2444,c_2955,
% 7.63/1.50                 c_3610,c_3637]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9113,plain,
% 7.63/1.50      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.63/1.50      inference(renaming,[status(thm)],[c_9112]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26936,plain,
% 7.63/1.50      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_26912,c_9113]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27009,plain,
% 7.63/1.50      ( sK2 = k1_xboole_0 ),
% 7.63/1.50      inference(equality_resolution_simp,[status(thm)],[c_26936]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27012,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_26935,c_27009]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27013,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(equality_resolution_simp,[status(thm)],[c_27012]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26937,plain,
% 7.63/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_26912,c_8886]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27005,plain,
% 7.63/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_26937,c_26959]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27007,plain,
% 7.63/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_27005,c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27017,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_27013,c_27007]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27018,plain,
% 7.63/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_27017,c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27029,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.63/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_27027,c_27018]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27033,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 7.63/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_27029,c_27007]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3,plain,
% 7.63/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1529,plain,
% 7.63/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6476,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 7.63/1.50      | sK1 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1529,c_6467]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1936,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 7.63/1.50      | ~ v1_relat_1(sK3)
% 7.63/1.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1938,plain,
% 7.63/1.50      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 7.63/1.50      | ~ v1_relat_1(sK3)
% 7.63/1.50      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1936]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2230,plain,
% 7.63/1.50      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10297,plain,
% 7.63/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_6476,c_37,c_1843,c_1938,c_2230]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27034,plain,
% 7.63/1.50      ( k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_27033,c_10297]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27035,plain,
% 7.63/1.50      ( $false ),
% 7.63/1.50      inference(equality_resolution_simp,[status(thm)],[c_27034]) ).
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  ------                               Statistics
% 7.63/1.50  
% 7.63/1.50  ------ General
% 7.63/1.50  
% 7.63/1.50  abstr_ref_over_cycles:                  0
% 7.63/1.50  abstr_ref_under_cycles:                 0
% 7.63/1.50  gc_basic_clause_elim:                   0
% 7.63/1.50  forced_gc_time:                         0
% 7.63/1.50  parsing_time:                           0.015
% 7.63/1.50  unif_index_cands_time:                  0.
% 7.63/1.50  unif_index_add_time:                    0.
% 7.63/1.50  orderings_time:                         0.
% 7.63/1.50  out_proof_time:                         0.014
% 7.63/1.50  total_time:                             0.676
% 7.63/1.50  num_of_symbols:                         49
% 7.63/1.50  num_of_terms:                           20259
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing
% 7.63/1.50  
% 7.63/1.50  num_of_splits:                          0
% 7.63/1.50  num_of_split_atoms:                     0
% 7.63/1.50  num_of_reused_defs:                     0
% 7.63/1.50  num_eq_ax_congr_red:                    4
% 7.63/1.50  num_of_sem_filtered_clauses:            1
% 7.63/1.50  num_of_subtypes:                        0
% 7.63/1.50  monotx_restored_types:                  0
% 7.63/1.50  sat_num_of_epr_types:                   0
% 7.63/1.50  sat_num_of_non_cyclic_types:            0
% 7.63/1.50  sat_guarded_non_collapsed_types:        0
% 7.63/1.50  num_pure_diseq_elim:                    0
% 7.63/1.50  simp_replaced_by:                       0
% 7.63/1.50  res_preprocessed:                       147
% 7.63/1.50  prep_upred:                             0
% 7.63/1.50  prep_unflattend:                        43
% 7.63/1.50  smt_new_axioms:                         0
% 7.63/1.50  pred_elim_cands:                        6
% 7.63/1.50  pred_elim:                              1
% 7.63/1.50  pred_elim_cl:                           -2
% 7.63/1.50  pred_elim_cycles:                       2
% 7.63/1.50  merged_defs:                            6
% 7.63/1.50  merged_defs_ncl:                        0
% 7.63/1.50  bin_hyper_res:                          6
% 7.63/1.50  prep_cycles:                            3
% 7.63/1.50  pred_elim_time:                         0.008
% 7.63/1.50  splitting_time:                         0.
% 7.63/1.50  sem_filter_time:                        0.
% 7.63/1.50  monotx_time:                            0.001
% 7.63/1.50  subtype_inf_time:                       0.
% 7.63/1.50  
% 7.63/1.50  ------ Problem properties
% 7.63/1.50  
% 7.63/1.50  clauses:                                40
% 7.63/1.50  conjectures:                            4
% 7.63/1.50  epr:                                    6
% 7.63/1.50  horn:                                   35
% 7.63/1.50  ground:                                 14
% 7.63/1.50  unary:                                  10
% 7.63/1.50  binary:                                 8
% 7.63/1.50  lits:                                   108
% 7.63/1.50  lits_eq:                                39
% 7.63/1.50  fd_pure:                                0
% 7.63/1.50  fd_pseudo:                              0
% 7.63/1.50  fd_cond:                                3
% 7.63/1.50  fd_pseudo_cond:                         1
% 7.63/1.50  ac_symbols:                             0
% 7.63/1.50  
% 7.63/1.50  ------ Propositional Solver
% 7.63/1.50  
% 7.63/1.50  prop_solver_calls:                      24
% 7.63/1.50  prop_fast_solver_calls:                 1778
% 7.63/1.50  smt_solver_calls:                       0
% 7.63/1.50  smt_fast_solver_calls:                  0
% 7.63/1.50  prop_num_of_clauses:                    9047
% 7.63/1.50  prop_preprocess_simplified:             18183
% 7.63/1.50  prop_fo_subsumed:                       70
% 7.63/1.50  prop_solver_time:                       0.
% 7.63/1.50  smt_solver_time:                        0.
% 7.63/1.50  smt_fast_solver_time:                   0.
% 7.63/1.50  prop_fast_solver_time:                  0.
% 7.63/1.50  prop_unsat_core_time:                   0.
% 7.63/1.50  
% 7.63/1.50  ------ QBF
% 7.63/1.50  
% 7.63/1.50  qbf_q_res:                              0
% 7.63/1.50  qbf_num_tautologies:                    0
% 7.63/1.50  qbf_prep_cycles:                        0
% 7.63/1.50  
% 7.63/1.50  ------ BMC1
% 7.63/1.50  
% 7.63/1.50  bmc1_current_bound:                     -1
% 7.63/1.50  bmc1_last_solved_bound:                 -1
% 7.63/1.50  bmc1_unsat_core_size:                   -1
% 7.63/1.50  bmc1_unsat_core_parents_size:           -1
% 7.63/1.50  bmc1_merge_next_fun:                    0
% 7.63/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation
% 7.63/1.50  
% 7.63/1.50  inst_num_of_clauses:                    2376
% 7.63/1.50  inst_num_in_passive:                    856
% 7.63/1.50  inst_num_in_active:                     1063
% 7.63/1.50  inst_num_in_unprocessed:                458
% 7.63/1.50  inst_num_of_loops:                      1410
% 7.63/1.50  inst_num_of_learning_restarts:          0
% 7.63/1.50  inst_num_moves_active_passive:          345
% 7.63/1.50  inst_lit_activity:                      0
% 7.63/1.50  inst_lit_activity_moves:                0
% 7.63/1.50  inst_num_tautologies:                   0
% 7.63/1.50  inst_num_prop_implied:                  0
% 7.63/1.50  inst_num_existing_simplified:           0
% 7.63/1.50  inst_num_eq_res_simplified:             0
% 7.63/1.50  inst_num_child_elim:                    0
% 7.63/1.50  inst_num_of_dismatching_blockings:      1371
% 7.63/1.50  inst_num_of_non_proper_insts:           2620
% 7.63/1.50  inst_num_of_duplicates:                 0
% 7.63/1.50  inst_inst_num_from_inst_to_res:         0
% 7.63/1.50  inst_dismatching_checking_time:         0.
% 7.63/1.50  
% 7.63/1.50  ------ Resolution
% 7.63/1.50  
% 7.63/1.50  res_num_of_clauses:                     0
% 7.63/1.50  res_num_in_passive:                     0
% 7.63/1.50  res_num_in_active:                      0
% 7.63/1.50  res_num_of_loops:                       150
% 7.63/1.50  res_forward_subset_subsumed:            87
% 7.63/1.50  res_backward_subset_subsumed:           4
% 7.63/1.50  res_forward_subsumed:                   0
% 7.63/1.50  res_backward_subsumed:                  0
% 7.63/1.50  res_forward_subsumption_resolution:     4
% 7.63/1.50  res_backward_subsumption_resolution:    0
% 7.63/1.50  res_clause_to_clause_subsumption:       2703
% 7.63/1.50  res_orphan_elimination:                 0
% 7.63/1.50  res_tautology_del:                      141
% 7.63/1.50  res_num_eq_res_simplified:              1
% 7.63/1.50  res_num_sel_changes:                    0
% 7.63/1.50  res_moves_from_active_to_pass:          0
% 7.63/1.50  
% 7.63/1.50  ------ Superposition
% 7.63/1.50  
% 7.63/1.50  sup_time_total:                         0.
% 7.63/1.50  sup_time_generating:                    0.
% 7.63/1.50  sup_time_sim_full:                      0.
% 7.63/1.50  sup_time_sim_immed:                     0.
% 7.63/1.50  
% 7.63/1.50  sup_num_of_clauses:                     572
% 7.63/1.50  sup_num_in_active:                      189
% 7.63/1.50  sup_num_in_passive:                     383
% 7.63/1.50  sup_num_of_loops:                       280
% 7.63/1.50  sup_fw_superposition:                   1083
% 7.63/1.50  sup_bw_superposition:                   741
% 7.63/1.50  sup_immediate_simplified:               672
% 7.63/1.50  sup_given_eliminated:                   8
% 7.63/1.50  comparisons_done:                       0
% 7.63/1.50  comparisons_avoided:                    313
% 7.63/1.50  
% 7.63/1.50  ------ Simplifications
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  sim_fw_subset_subsumed:                 66
% 7.63/1.50  sim_bw_subset_subsumed:                 73
% 7.63/1.50  sim_fw_subsumed:                        216
% 7.63/1.50  sim_bw_subsumed:                        64
% 7.63/1.50  sim_fw_subsumption_res:                 20
% 7.63/1.50  sim_bw_subsumption_res:                 0
% 7.63/1.50  sim_tautology_del:                      99
% 7.63/1.50  sim_eq_tautology_del:                   118
% 7.63/1.50  sim_eq_res_simp:                        6
% 7.63/1.50  sim_fw_demodulated:                     212
% 7.63/1.50  sim_bw_demodulated:                     71
% 7.63/1.50  sim_light_normalised:                   294
% 7.63/1.50  sim_joinable_taut:                      0
% 7.63/1.50  sim_joinable_simp:                      0
% 7.63/1.50  sim_ac_normalised:                      0
% 7.63/1.50  sim_smt_subsumption:                    0
% 7.63/1.50  
%------------------------------------------------------------------------------
