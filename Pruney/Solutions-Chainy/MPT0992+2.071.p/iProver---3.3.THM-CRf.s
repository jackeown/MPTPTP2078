%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:01 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  206 (4631 expanded)
%              Number of clauses        :  135 (1562 expanded)
%              Number of leaves         :   17 ( 870 expanded)
%              Depth                    :   25
%              Number of atoms          :  653 (25656 expanded)
%              Number of equality atoms :  364 (6833 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f39])).

fof(f69,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1843,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_692,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_694,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_28])).

cnf(c_1842,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1848,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2585,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1842,c_1848])).

cnf(c_2603,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_694,c_2585])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1849,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2769,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_1849])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2090,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2321,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2322,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2564,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2565,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_2774,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2769,c_33,c_2322,c_2565])).

cnf(c_2775,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2774])).

cnf(c_2783,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1843,c_2775])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4616,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_1844])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1845,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3269,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1845])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2297,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_3364,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_30,c_28,c_2297])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4041,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_1847])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4210,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4041,c_31,c_33])).

cnf(c_1851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4218,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4210,c_1851])).

cnf(c_4346,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4218,c_2565])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3169,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1846])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2520,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2521,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_3356,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3169,c_31,c_33,c_2521])).

cnf(c_3373,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3364,c_3356])).

cnf(c_5411,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4616,c_4346,c_3373])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_702,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_703,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_6])).

cnf(c_715,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_703,c_319])).

cnf(c_1830,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_720,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_2275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_2303,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_31,c_33,c_720,c_2276])).

cnf(c_2304,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2303])).

cnf(c_3370,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3364,c_2304])).

cnf(c_3502,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_3370])).

cnf(c_5422,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5411,c_3502])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_4221,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4210,c_1839])).

cnf(c_4447,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4221,c_2565,c_4218])).

cnf(c_5566,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5422,c_4346,c_4447])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5586,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5566,c_26])).

cnf(c_5587,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5586])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_1840,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_2908,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1840])).

cnf(c_2932,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2908,c_33,c_2322,c_2565])).

cnf(c_5740,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_5587,c_2932])).

cnf(c_5573,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5566,c_4210])).

cnf(c_5641,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5573,c_5587])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5643,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5641,c_2])).

cnf(c_721,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_721])).

cnf(c_1829,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_3371,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3364,c_1829])).

cnf(c_3388,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3371,c_3373])).

cnf(c_5575,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5566,c_3388])).

cnf(c_13,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_518,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_519,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1838,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2008,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_1])).

cnf(c_2419,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2008,c_31,c_33,c_2276])).

cnf(c_2420,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2419])).

cnf(c_3369,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3364,c_2420])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_338,plain,
    ( sK2 != X0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_339,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1415,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2219,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1416,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2116,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2369,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_571,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1836,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1912,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1836,c_1])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2114,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2360,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_2361,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_2442,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2443,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_2516,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1912,c_26,c_95,c_96,c_2360,c_2361,c_2443])).

cnf(c_2517,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2516])).

cnf(c_3631,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_339,c_2219,c_2369,c_2517])).

cnf(c_5577,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5566,c_3631])).

cnf(c_5614,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5577])).

cnf(c_5632,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5575,c_5587,c_5614])).

cnf(c_5633,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5632])).

cnf(c_5636,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5633,c_2])).

cnf(c_5645,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5643,c_5636])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5740,c_5645])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.01  
% 2.78/1.01  ------  iProver source info
% 2.78/1.01  
% 2.78/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.01  git: non_committed_changes: false
% 2.78/1.01  git: last_make_outside_of_git: false
% 2.78/1.01  
% 2.78/1.01  ------ 
% 2.78/1.01  
% 2.78/1.01  ------ Input Options
% 2.78/1.01  
% 2.78/1.01  --out_options                           all
% 2.78/1.01  --tptp_safe_out                         true
% 2.78/1.01  --problem_path                          ""
% 2.78/1.01  --include_path                          ""
% 2.78/1.01  --clausifier                            res/vclausify_rel
% 2.78/1.01  --clausifier_options                    --mode clausify
% 2.78/1.01  --stdin                                 false
% 2.78/1.01  --stats_out                             all
% 2.78/1.01  
% 2.78/1.01  ------ General Options
% 2.78/1.01  
% 2.78/1.01  --fof                                   false
% 2.78/1.01  --time_out_real                         305.
% 2.78/1.01  --time_out_virtual                      -1.
% 2.78/1.01  --symbol_type_check                     false
% 2.78/1.01  --clausify_out                          false
% 2.78/1.01  --sig_cnt_out                           false
% 2.78/1.01  --trig_cnt_out                          false
% 2.78/1.01  --trig_cnt_out_tolerance                1.
% 2.78/1.01  --trig_cnt_out_sk_spl                   false
% 2.78/1.01  --abstr_cl_out                          false
% 2.78/1.01  
% 2.78/1.01  ------ Global Options
% 2.78/1.01  
% 2.78/1.01  --schedule                              default
% 2.78/1.01  --add_important_lit                     false
% 2.78/1.01  --prop_solver_per_cl                    1000
% 2.78/1.01  --min_unsat_core                        false
% 2.78/1.01  --soft_assumptions                      false
% 2.78/1.01  --soft_lemma_size                       3
% 2.78/1.01  --prop_impl_unit_size                   0
% 2.78/1.01  --prop_impl_unit                        []
% 2.78/1.01  --share_sel_clauses                     true
% 2.78/1.01  --reset_solvers                         false
% 2.78/1.01  --bc_imp_inh                            [conj_cone]
% 2.78/1.01  --conj_cone_tolerance                   3.
% 2.78/1.01  --extra_neg_conj                        none
% 2.78/1.01  --large_theory_mode                     true
% 2.78/1.01  --prolific_symb_bound                   200
% 2.78/1.01  --lt_threshold                          2000
% 2.78/1.01  --clause_weak_htbl                      true
% 2.78/1.01  --gc_record_bc_elim                     false
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing Options
% 2.78/1.01  
% 2.78/1.01  --preprocessing_flag                    true
% 2.78/1.01  --time_out_prep_mult                    0.1
% 2.78/1.01  --splitting_mode                        input
% 2.78/1.01  --splitting_grd                         true
% 2.78/1.01  --splitting_cvd                         false
% 2.78/1.01  --splitting_cvd_svl                     false
% 2.78/1.01  --splitting_nvd                         32
% 2.78/1.01  --sub_typing                            true
% 2.78/1.01  --prep_gs_sim                           true
% 2.78/1.01  --prep_unflatten                        true
% 2.78/1.01  --prep_res_sim                          true
% 2.78/1.01  --prep_upred                            true
% 2.78/1.01  --prep_sem_filter                       exhaustive
% 2.78/1.01  --prep_sem_filter_out                   false
% 2.78/1.01  --pred_elim                             true
% 2.78/1.01  --res_sim_input                         true
% 2.78/1.01  --eq_ax_congr_red                       true
% 2.78/1.01  --pure_diseq_elim                       true
% 2.78/1.01  --brand_transform                       false
% 2.78/1.01  --non_eq_to_eq                          false
% 2.78/1.01  --prep_def_merge                        true
% 2.78/1.01  --prep_def_merge_prop_impl              false
% 2.78/1.01  --prep_def_merge_mbd                    true
% 2.78/1.01  --prep_def_merge_tr_red                 false
% 2.78/1.01  --prep_def_merge_tr_cl                  false
% 2.78/1.01  --smt_preprocessing                     true
% 2.78/1.01  --smt_ac_axioms                         fast
% 2.78/1.01  --preprocessed_out                      false
% 2.78/1.01  --preprocessed_stats                    false
% 2.78/1.01  
% 2.78/1.01  ------ Abstraction refinement Options
% 2.78/1.01  
% 2.78/1.01  --abstr_ref                             []
% 2.78/1.01  --abstr_ref_prep                        false
% 2.78/1.01  --abstr_ref_until_sat                   false
% 2.78/1.01  --abstr_ref_sig_restrict                funpre
% 2.78/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.01  --abstr_ref_under                       []
% 2.78/1.01  
% 2.78/1.01  ------ SAT Options
% 2.78/1.01  
% 2.78/1.01  --sat_mode                              false
% 2.78/1.01  --sat_fm_restart_options                ""
% 2.78/1.01  --sat_gr_def                            false
% 2.78/1.01  --sat_epr_types                         true
% 2.78/1.01  --sat_non_cyclic_types                  false
% 2.78/1.01  --sat_finite_models                     false
% 2.78/1.01  --sat_fm_lemmas                         false
% 2.78/1.01  --sat_fm_prep                           false
% 2.78/1.01  --sat_fm_uc_incr                        true
% 2.78/1.01  --sat_out_model                         small
% 2.78/1.01  --sat_out_clauses                       false
% 2.78/1.01  
% 2.78/1.01  ------ QBF Options
% 2.78/1.01  
% 2.78/1.01  --qbf_mode                              false
% 2.78/1.01  --qbf_elim_univ                         false
% 2.78/1.01  --qbf_dom_inst                          none
% 2.78/1.01  --qbf_dom_pre_inst                      false
% 2.78/1.01  --qbf_sk_in                             false
% 2.78/1.01  --qbf_pred_elim                         true
% 2.78/1.01  --qbf_split                             512
% 2.78/1.01  
% 2.78/1.01  ------ BMC1 Options
% 2.78/1.01  
% 2.78/1.01  --bmc1_incremental                      false
% 2.78/1.01  --bmc1_axioms                           reachable_all
% 2.78/1.01  --bmc1_min_bound                        0
% 2.78/1.01  --bmc1_max_bound                        -1
% 2.78/1.01  --bmc1_max_bound_default                -1
% 2.78/1.01  --bmc1_symbol_reachability              true
% 2.78/1.01  --bmc1_property_lemmas                  false
% 2.78/1.01  --bmc1_k_induction                      false
% 2.78/1.01  --bmc1_non_equiv_states                 false
% 2.78/1.01  --bmc1_deadlock                         false
% 2.78/1.01  --bmc1_ucm                              false
% 2.78/1.01  --bmc1_add_unsat_core                   none
% 2.78/1.01  --bmc1_unsat_core_children              false
% 2.78/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.01  --bmc1_out_stat                         full
% 2.78/1.01  --bmc1_ground_init                      false
% 2.78/1.01  --bmc1_pre_inst_next_state              false
% 2.78/1.01  --bmc1_pre_inst_state                   false
% 2.78/1.01  --bmc1_pre_inst_reach_state             false
% 2.78/1.01  --bmc1_out_unsat_core                   false
% 2.78/1.01  --bmc1_aig_witness_out                  false
% 2.78/1.01  --bmc1_verbose                          false
% 2.78/1.01  --bmc1_dump_clauses_tptp                false
% 2.78/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.01  --bmc1_dump_file                        -
% 2.78/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.01  --bmc1_ucm_extend_mode                  1
% 2.78/1.01  --bmc1_ucm_init_mode                    2
% 2.78/1.01  --bmc1_ucm_cone_mode                    none
% 2.78/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.01  --bmc1_ucm_relax_model                  4
% 2.78/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.01  --bmc1_ucm_layered_model                none
% 2.78/1.01  --bmc1_ucm_max_lemma_size               10
% 2.78/1.01  
% 2.78/1.01  ------ AIG Options
% 2.78/1.01  
% 2.78/1.01  --aig_mode                              false
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation Options
% 2.78/1.01  
% 2.78/1.01  --instantiation_flag                    true
% 2.78/1.01  --inst_sos_flag                         false
% 2.78/1.01  --inst_sos_phase                        true
% 2.78/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel_side                     num_symb
% 2.78/1.01  --inst_solver_per_active                1400
% 2.78/1.01  --inst_solver_calls_frac                1.
% 2.78/1.01  --inst_passive_queue_type               priority_queues
% 2.78/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.01  --inst_passive_queues_freq              [25;2]
% 2.78/1.01  --inst_dismatching                      true
% 2.78/1.01  --inst_eager_unprocessed_to_passive     true
% 2.78/1.01  --inst_prop_sim_given                   true
% 2.78/1.01  --inst_prop_sim_new                     false
% 2.78/1.01  --inst_subs_new                         false
% 2.78/1.01  --inst_eq_res_simp                      false
% 2.78/1.01  --inst_subs_given                       false
% 2.78/1.01  --inst_orphan_elimination               true
% 2.78/1.01  --inst_learning_loop_flag               true
% 2.78/1.01  --inst_learning_start                   3000
% 2.78/1.01  --inst_learning_factor                  2
% 2.78/1.01  --inst_start_prop_sim_after_learn       3
% 2.78/1.01  --inst_sel_renew                        solver
% 2.78/1.01  --inst_lit_activity_flag                true
% 2.78/1.01  --inst_restr_to_given                   false
% 2.78/1.01  --inst_activity_threshold               500
% 2.78/1.01  --inst_out_proof                        true
% 2.78/1.01  
% 2.78/1.01  ------ Resolution Options
% 2.78/1.01  
% 2.78/1.01  --resolution_flag                       true
% 2.78/1.01  --res_lit_sel                           adaptive
% 2.78/1.01  --res_lit_sel_side                      none
% 2.78/1.01  --res_ordering                          kbo
% 2.78/1.01  --res_to_prop_solver                    active
% 2.78/1.01  --res_prop_simpl_new                    false
% 2.78/1.01  --res_prop_simpl_given                  true
% 2.78/1.01  --res_passive_queue_type                priority_queues
% 2.78/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.01  --res_passive_queues_freq               [15;5]
% 2.78/1.01  --res_forward_subs                      full
% 2.78/1.01  --res_backward_subs                     full
% 2.78/1.01  --res_forward_subs_resolution           true
% 2.78/1.01  --res_backward_subs_resolution          true
% 2.78/1.01  --res_orphan_elimination                true
% 2.78/1.01  --res_time_limit                        2.
% 2.78/1.01  --res_out_proof                         true
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Options
% 2.78/1.01  
% 2.78/1.01  --superposition_flag                    true
% 2.78/1.01  --sup_passive_queue_type                priority_queues
% 2.78/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.01  --demod_completeness_check              fast
% 2.78/1.01  --demod_use_ground                      true
% 2.78/1.01  --sup_to_prop_solver                    passive
% 2.78/1.01  --sup_prop_simpl_new                    true
% 2.78/1.01  --sup_prop_simpl_given                  true
% 2.78/1.01  --sup_fun_splitting                     false
% 2.78/1.01  --sup_smt_interval                      50000
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Simplification Setup
% 2.78/1.01  
% 2.78/1.01  --sup_indices_passive                   []
% 2.78/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_full_bw                           [BwDemod]
% 2.78/1.01  --sup_immed_triv                        [TrivRules]
% 2.78/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_immed_bw_main                     []
% 2.78/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  
% 2.78/1.01  ------ Combination Options
% 2.78/1.01  
% 2.78/1.01  --comb_res_mult                         3
% 2.78/1.01  --comb_sup_mult                         2
% 2.78/1.01  --comb_inst_mult                        10
% 2.78/1.01  
% 2.78/1.01  ------ Debug Options
% 2.78/1.01  
% 2.78/1.01  --dbg_backtrace                         false
% 2.78/1.01  --dbg_dump_prop_clauses                 false
% 2.78/1.01  --dbg_dump_prop_clauses_file            -
% 2.78/1.01  --dbg_out_stat                          false
% 2.78/1.01  ------ Parsing...
% 2.78/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.01  ------ Proving...
% 2.78/1.01  ------ Problem Properties 
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  clauses                                 29
% 2.78/1.01  conjectures                             4
% 2.78/1.01  EPR                                     4
% 2.78/1.01  Horn                                    24
% 2.78/1.01  unary                                   6
% 2.78/1.01  binary                                  4
% 2.78/1.01  lits                                    87
% 2.78/1.01  lits eq                                 35
% 2.78/1.01  fd_pure                                 0
% 2.78/1.01  fd_pseudo                               0
% 2.78/1.01  fd_cond                                 4
% 2.78/1.01  fd_pseudo_cond                          0
% 2.78/1.01  AC symbols                              0
% 2.78/1.01  
% 2.78/1.01  ------ Schedule dynamic 5 is on 
% 2.78/1.01  
% 2.78/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  ------ 
% 2.78/1.01  Current options:
% 2.78/1.01  ------ 
% 2.78/1.01  
% 2.78/1.01  ------ Input Options
% 2.78/1.01  
% 2.78/1.01  --out_options                           all
% 2.78/1.01  --tptp_safe_out                         true
% 2.78/1.01  --problem_path                          ""
% 2.78/1.01  --include_path                          ""
% 2.78/1.01  --clausifier                            res/vclausify_rel
% 2.78/1.01  --clausifier_options                    --mode clausify
% 2.78/1.01  --stdin                                 false
% 2.78/1.01  --stats_out                             all
% 2.78/1.01  
% 2.78/1.01  ------ General Options
% 2.78/1.01  
% 2.78/1.01  --fof                                   false
% 2.78/1.01  --time_out_real                         305.
% 2.78/1.01  --time_out_virtual                      -1.
% 2.78/1.01  --symbol_type_check                     false
% 2.78/1.01  --clausify_out                          false
% 2.78/1.01  --sig_cnt_out                           false
% 2.78/1.01  --trig_cnt_out                          false
% 2.78/1.01  --trig_cnt_out_tolerance                1.
% 2.78/1.01  --trig_cnt_out_sk_spl                   false
% 2.78/1.01  --abstr_cl_out                          false
% 2.78/1.01  
% 2.78/1.01  ------ Global Options
% 2.78/1.01  
% 2.78/1.01  --schedule                              default
% 2.78/1.01  --add_important_lit                     false
% 2.78/1.01  --prop_solver_per_cl                    1000
% 2.78/1.01  --min_unsat_core                        false
% 2.78/1.01  --soft_assumptions                      false
% 2.78/1.01  --soft_lemma_size                       3
% 2.78/1.01  --prop_impl_unit_size                   0
% 2.78/1.01  --prop_impl_unit                        []
% 2.78/1.01  --share_sel_clauses                     true
% 2.78/1.01  --reset_solvers                         false
% 2.78/1.01  --bc_imp_inh                            [conj_cone]
% 2.78/1.01  --conj_cone_tolerance                   3.
% 2.78/1.01  --extra_neg_conj                        none
% 2.78/1.01  --large_theory_mode                     true
% 2.78/1.01  --prolific_symb_bound                   200
% 2.78/1.01  --lt_threshold                          2000
% 2.78/1.01  --clause_weak_htbl                      true
% 2.78/1.01  --gc_record_bc_elim                     false
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing Options
% 2.78/1.01  
% 2.78/1.01  --preprocessing_flag                    true
% 2.78/1.01  --time_out_prep_mult                    0.1
% 2.78/1.01  --splitting_mode                        input
% 2.78/1.01  --splitting_grd                         true
% 2.78/1.01  --splitting_cvd                         false
% 2.78/1.01  --splitting_cvd_svl                     false
% 2.78/1.01  --splitting_nvd                         32
% 2.78/1.01  --sub_typing                            true
% 2.78/1.01  --prep_gs_sim                           true
% 2.78/1.01  --prep_unflatten                        true
% 2.78/1.01  --prep_res_sim                          true
% 2.78/1.01  --prep_upred                            true
% 2.78/1.01  --prep_sem_filter                       exhaustive
% 2.78/1.01  --prep_sem_filter_out                   false
% 2.78/1.01  --pred_elim                             true
% 2.78/1.01  --res_sim_input                         true
% 2.78/1.01  --eq_ax_congr_red                       true
% 2.78/1.01  --pure_diseq_elim                       true
% 2.78/1.01  --brand_transform                       false
% 2.78/1.01  --non_eq_to_eq                          false
% 2.78/1.01  --prep_def_merge                        true
% 2.78/1.01  --prep_def_merge_prop_impl              false
% 2.78/1.01  --prep_def_merge_mbd                    true
% 2.78/1.01  --prep_def_merge_tr_red                 false
% 2.78/1.01  --prep_def_merge_tr_cl                  false
% 2.78/1.01  --smt_preprocessing                     true
% 2.78/1.01  --smt_ac_axioms                         fast
% 2.78/1.01  --preprocessed_out                      false
% 2.78/1.01  --preprocessed_stats                    false
% 2.78/1.01  
% 2.78/1.01  ------ Abstraction refinement Options
% 2.78/1.01  
% 2.78/1.01  --abstr_ref                             []
% 2.78/1.01  --abstr_ref_prep                        false
% 2.78/1.01  --abstr_ref_until_sat                   false
% 2.78/1.01  --abstr_ref_sig_restrict                funpre
% 2.78/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.01  --abstr_ref_under                       []
% 2.78/1.01  
% 2.78/1.01  ------ SAT Options
% 2.78/1.01  
% 2.78/1.01  --sat_mode                              false
% 2.78/1.01  --sat_fm_restart_options                ""
% 2.78/1.01  --sat_gr_def                            false
% 2.78/1.01  --sat_epr_types                         true
% 2.78/1.01  --sat_non_cyclic_types                  false
% 2.78/1.01  --sat_finite_models                     false
% 2.78/1.01  --sat_fm_lemmas                         false
% 2.78/1.01  --sat_fm_prep                           false
% 2.78/1.01  --sat_fm_uc_incr                        true
% 2.78/1.01  --sat_out_model                         small
% 2.78/1.01  --sat_out_clauses                       false
% 2.78/1.01  
% 2.78/1.01  ------ QBF Options
% 2.78/1.01  
% 2.78/1.01  --qbf_mode                              false
% 2.78/1.01  --qbf_elim_univ                         false
% 2.78/1.01  --qbf_dom_inst                          none
% 2.78/1.01  --qbf_dom_pre_inst                      false
% 2.78/1.01  --qbf_sk_in                             false
% 2.78/1.01  --qbf_pred_elim                         true
% 2.78/1.01  --qbf_split                             512
% 2.78/1.01  
% 2.78/1.01  ------ BMC1 Options
% 2.78/1.01  
% 2.78/1.01  --bmc1_incremental                      false
% 2.78/1.01  --bmc1_axioms                           reachable_all
% 2.78/1.01  --bmc1_min_bound                        0
% 2.78/1.01  --bmc1_max_bound                        -1
% 2.78/1.01  --bmc1_max_bound_default                -1
% 2.78/1.01  --bmc1_symbol_reachability              true
% 2.78/1.01  --bmc1_property_lemmas                  false
% 2.78/1.01  --bmc1_k_induction                      false
% 2.78/1.01  --bmc1_non_equiv_states                 false
% 2.78/1.01  --bmc1_deadlock                         false
% 2.78/1.01  --bmc1_ucm                              false
% 2.78/1.01  --bmc1_add_unsat_core                   none
% 2.78/1.01  --bmc1_unsat_core_children              false
% 2.78/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.01  --bmc1_out_stat                         full
% 2.78/1.01  --bmc1_ground_init                      false
% 2.78/1.01  --bmc1_pre_inst_next_state              false
% 2.78/1.01  --bmc1_pre_inst_state                   false
% 2.78/1.01  --bmc1_pre_inst_reach_state             false
% 2.78/1.01  --bmc1_out_unsat_core                   false
% 2.78/1.01  --bmc1_aig_witness_out                  false
% 2.78/1.01  --bmc1_verbose                          false
% 2.78/1.01  --bmc1_dump_clauses_tptp                false
% 2.78/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.01  --bmc1_dump_file                        -
% 2.78/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.01  --bmc1_ucm_extend_mode                  1
% 2.78/1.01  --bmc1_ucm_init_mode                    2
% 2.78/1.01  --bmc1_ucm_cone_mode                    none
% 2.78/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.01  --bmc1_ucm_relax_model                  4
% 2.78/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.01  --bmc1_ucm_layered_model                none
% 2.78/1.01  --bmc1_ucm_max_lemma_size               10
% 2.78/1.01  
% 2.78/1.01  ------ AIG Options
% 2.78/1.01  
% 2.78/1.01  --aig_mode                              false
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation Options
% 2.78/1.01  
% 2.78/1.01  --instantiation_flag                    true
% 2.78/1.01  --inst_sos_flag                         false
% 2.78/1.01  --inst_sos_phase                        true
% 2.78/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel_side                     none
% 2.78/1.01  --inst_solver_per_active                1400
% 2.78/1.01  --inst_solver_calls_frac                1.
% 2.78/1.01  --inst_passive_queue_type               priority_queues
% 2.78/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.01  --inst_passive_queues_freq              [25;2]
% 2.78/1.01  --inst_dismatching                      true
% 2.78/1.01  --inst_eager_unprocessed_to_passive     true
% 2.78/1.01  --inst_prop_sim_given                   true
% 2.78/1.01  --inst_prop_sim_new                     false
% 2.78/1.01  --inst_subs_new                         false
% 2.78/1.01  --inst_eq_res_simp                      false
% 2.78/1.01  --inst_subs_given                       false
% 2.78/1.01  --inst_orphan_elimination               true
% 2.78/1.01  --inst_learning_loop_flag               true
% 2.78/1.01  --inst_learning_start                   3000
% 2.78/1.01  --inst_learning_factor                  2
% 2.78/1.01  --inst_start_prop_sim_after_learn       3
% 2.78/1.01  --inst_sel_renew                        solver
% 2.78/1.01  --inst_lit_activity_flag                true
% 2.78/1.01  --inst_restr_to_given                   false
% 2.78/1.01  --inst_activity_threshold               500
% 2.78/1.01  --inst_out_proof                        true
% 2.78/1.01  
% 2.78/1.01  ------ Resolution Options
% 2.78/1.01  
% 2.78/1.01  --resolution_flag                       false
% 2.78/1.01  --res_lit_sel                           adaptive
% 2.78/1.01  --res_lit_sel_side                      none
% 2.78/1.01  --res_ordering                          kbo
% 2.78/1.01  --res_to_prop_solver                    active
% 2.78/1.01  --res_prop_simpl_new                    false
% 2.78/1.01  --res_prop_simpl_given                  true
% 2.78/1.01  --res_passive_queue_type                priority_queues
% 2.78/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.01  --res_passive_queues_freq               [15;5]
% 2.78/1.01  --res_forward_subs                      full
% 2.78/1.01  --res_backward_subs                     full
% 2.78/1.01  --res_forward_subs_resolution           true
% 2.78/1.01  --res_backward_subs_resolution          true
% 2.78/1.01  --res_orphan_elimination                true
% 2.78/1.01  --res_time_limit                        2.
% 2.78/1.01  --res_out_proof                         true
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Options
% 2.78/1.01  
% 2.78/1.01  --superposition_flag                    true
% 2.78/1.01  --sup_passive_queue_type                priority_queues
% 2.78/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.01  --demod_completeness_check              fast
% 2.78/1.01  --demod_use_ground                      true
% 2.78/1.01  --sup_to_prop_solver                    passive
% 2.78/1.01  --sup_prop_simpl_new                    true
% 2.78/1.01  --sup_prop_simpl_given                  true
% 2.78/1.01  --sup_fun_splitting                     false
% 2.78/1.01  --sup_smt_interval                      50000
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Simplification Setup
% 2.78/1.01  
% 2.78/1.01  --sup_indices_passive                   []
% 2.78/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_full_bw                           [BwDemod]
% 2.78/1.01  --sup_immed_triv                        [TrivRules]
% 2.78/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_immed_bw_main                     []
% 2.78/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  
% 2.78/1.01  ------ Combination Options
% 2.78/1.01  
% 2.78/1.01  --comb_res_mult                         3
% 2.78/1.01  --comb_sup_mult                         2
% 2.78/1.01  --comb_inst_mult                        10
% 2.78/1.01  
% 2.78/1.01  ------ Debug Options
% 2.78/1.01  
% 2.78/1.01  --dbg_backtrace                         false
% 2.78/1.01  --dbg_dump_prop_clauses                 false
% 2.78/1.01  --dbg_dump_prop_clauses_file            -
% 2.78/1.01  --dbg_out_stat                          false
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  ------ Proving...
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS status Theorem for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  fof(f14,conjecture,(
% 2.78/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f15,negated_conjecture,(
% 2.78/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.78/1.01    inference(negated_conjecture,[],[f14])).
% 2.78/1.01  
% 2.78/1.01  fof(f33,plain,(
% 2.78/1.01    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.78/1.01    inference(ennf_transformation,[],[f15])).
% 2.78/1.01  
% 2.78/1.01  fof(f34,plain,(
% 2.78/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.78/1.01    inference(flattening,[],[f33])).
% 2.78/1.01  
% 2.78/1.01  fof(f39,plain,(
% 2.78/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.78/1.01    introduced(choice_axiom,[])).
% 2.78/1.01  
% 2.78/1.01  fof(f40,plain,(
% 2.78/1.01    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.78/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f39])).
% 2.78/1.01  
% 2.78/1.01  fof(f69,plain,(
% 2.78/1.01    r1_tarski(sK2,sK0)),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f10,axiom,(
% 2.78/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f25,plain,(
% 2.78/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.01    inference(ennf_transformation,[],[f10])).
% 2.78/1.01  
% 2.78/1.01  fof(f26,plain,(
% 2.78/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.01    inference(flattening,[],[f25])).
% 2.78/1.01  
% 2.78/1.01  fof(f38,plain,(
% 2.78/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.01    inference(nnf_transformation,[],[f26])).
% 2.78/1.01  
% 2.78/1.01  fof(f54,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f38])).
% 2.78/1.01  
% 2.78/1.01  fof(f67,plain,(
% 2.78/1.01    v1_funct_2(sK3,sK0,sK1)),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f68,plain,(
% 2.78/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f9,axiom,(
% 2.78/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f24,plain,(
% 2.78/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.01    inference(ennf_transformation,[],[f9])).
% 2.78/1.01  
% 2.78/1.01  fof(f53,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f24])).
% 2.78/1.01  
% 2.78/1.01  fof(f7,axiom,(
% 2.78/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f21,plain,(
% 2.78/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(ennf_transformation,[],[f7])).
% 2.78/1.01  
% 2.78/1.01  fof(f22,plain,(
% 2.78/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(flattening,[],[f21])).
% 2.78/1.01  
% 2.78/1.01  fof(f50,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f22])).
% 2.78/1.01  
% 2.78/1.01  fof(f3,axiom,(
% 2.78/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f17,plain,(
% 2.78/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.78/1.01    inference(ennf_transformation,[],[f3])).
% 2.78/1.01  
% 2.78/1.01  fof(f45,plain,(
% 2.78/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f17])).
% 2.78/1.01  
% 2.78/1.01  fof(f5,axiom,(
% 2.78/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f48,plain,(
% 2.78/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f5])).
% 2.78/1.01  
% 2.78/1.01  fof(f13,axiom,(
% 2.78/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f31,plain,(
% 2.78/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.78/1.01    inference(ennf_transformation,[],[f13])).
% 2.78/1.01  
% 2.78/1.01  fof(f32,plain,(
% 2.78/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(flattening,[],[f31])).
% 2.78/1.01  
% 2.78/1.01  fof(f65,plain,(
% 2.78/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f32])).
% 2.78/1.01  
% 2.78/1.01  fof(f12,axiom,(
% 2.78/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f29,plain,(
% 2.78/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.78/1.01    inference(ennf_transformation,[],[f12])).
% 2.78/1.01  
% 2.78/1.01  fof(f30,plain,(
% 2.78/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.78/1.01    inference(flattening,[],[f29])).
% 2.78/1.01  
% 2.78/1.01  fof(f62,plain,(
% 2.78/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f30])).
% 2.78/1.01  
% 2.78/1.01  fof(f66,plain,(
% 2.78/1.01    v1_funct_1(sK3)),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f11,axiom,(
% 2.78/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f27,plain,(
% 2.78/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.78/1.01    inference(ennf_transformation,[],[f11])).
% 2.78/1.01  
% 2.78/1.01  fof(f28,plain,(
% 2.78/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.78/1.01    inference(flattening,[],[f27])).
% 2.78/1.01  
% 2.78/1.01  fof(f61,plain,(
% 2.78/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f28])).
% 2.78/1.01  
% 2.78/1.01  fof(f60,plain,(
% 2.78/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f28])).
% 2.78/1.01  
% 2.78/1.01  fof(f64,plain,(
% 2.78/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f32])).
% 2.78/1.01  
% 2.78/1.01  fof(f71,plain,(
% 2.78/1.01    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f8,axiom,(
% 2.78/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f23,plain,(
% 2.78/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.01    inference(ennf_transformation,[],[f8])).
% 2.78/1.01  
% 2.78/1.01  fof(f52,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f23])).
% 2.78/1.01  
% 2.78/1.01  fof(f4,axiom,(
% 2.78/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f18,plain,(
% 2.78/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(ennf_transformation,[],[f4])).
% 2.78/1.01  
% 2.78/1.01  fof(f37,plain,(
% 2.78/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(nnf_transformation,[],[f18])).
% 2.78/1.01  
% 2.78/1.01  fof(f46,plain,(
% 2.78/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f37])).
% 2.78/1.01  
% 2.78/1.01  fof(f70,plain,(
% 2.78/1.01    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f51,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f23])).
% 2.78/1.01  
% 2.78/1.01  fof(f6,axiom,(
% 2.78/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f19,plain,(
% 2.78/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/1.01    inference(ennf_transformation,[],[f6])).
% 2.78/1.01  
% 2.78/1.01  fof(f20,plain,(
% 2.78/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.01    inference(flattening,[],[f19])).
% 2.78/1.01  
% 2.78/1.01  fof(f49,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f20])).
% 2.78/1.01  
% 2.78/1.01  fof(f2,axiom,(
% 2.78/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f35,plain,(
% 2.78/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.78/1.01    inference(nnf_transformation,[],[f2])).
% 2.78/1.01  
% 2.78/1.01  fof(f36,plain,(
% 2.78/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.78/1.01    inference(flattening,[],[f35])).
% 2.78/1.01  
% 2.78/1.01  fof(f43,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.78/1.01    inference(cnf_transformation,[],[f36])).
% 2.78/1.01  
% 2.78/1.01  fof(f73,plain,(
% 2.78/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.78/1.01    inference(equality_resolution,[],[f43])).
% 2.78/1.01  
% 2.78/1.01  fof(f59,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f38])).
% 2.78/1.01  
% 2.78/1.01  fof(f74,plain,(
% 2.78/1.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(equality_resolution,[],[f59])).
% 2.78/1.01  
% 2.78/1.01  fof(f75,plain,(
% 2.78/1.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.78/1.01    inference(equality_resolution,[],[f74])).
% 2.78/1.01  
% 2.78/1.01  fof(f44,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.78/1.01    inference(cnf_transformation,[],[f36])).
% 2.78/1.01  
% 2.78/1.01  fof(f72,plain,(
% 2.78/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.78/1.01    inference(equality_resolution,[],[f44])).
% 2.78/1.01  
% 2.78/1.01  fof(f1,axiom,(
% 2.78/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f16,plain,(
% 2.78/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.78/1.01    inference(ennf_transformation,[],[f1])).
% 2.78/1.01  
% 2.78/1.01  fof(f41,plain,(
% 2.78/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f16])).
% 2.78/1.01  
% 2.78/1.01  fof(f58,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f38])).
% 2.78/1.01  
% 2.78/1.01  fof(f76,plain,(
% 2.78/1.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.78/1.01    inference(equality_resolution,[],[f58])).
% 2.78/1.01  
% 2.78/1.01  fof(f42,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f36])).
% 2.78/1.01  
% 2.78/1.01  cnf(c_27,negated_conjecture,
% 2.78/1.01      ( r1_tarski(sK2,sK0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1843,plain,
% 2.78/1.01      ( r1_tarski(sK2,sK0) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_18,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.78/1.01      | k1_xboole_0 = X2 ),
% 2.78/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_29,negated_conjecture,
% 2.78/1.01      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_691,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.78/1.01      | sK3 != X0
% 2.78/1.01      | sK1 != X2
% 2.78/1.01      | sK0 != X1
% 2.78/1.01      | k1_xboole_0 = X2 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_692,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.01      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.78/1.01      | k1_xboole_0 = sK1 ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_28,negated_conjecture,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_694,plain,
% 2.78/1.01      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_692,c_28]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1842,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_12,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1848,plain,
% 2.78/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2585,plain,
% 2.78/1.01      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1842,c_1848]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2603,plain,
% 2.78/1.01      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_694,c_2585]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_9,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.78/1.01      | ~ v1_relat_1(X1)
% 2.78/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1849,plain,
% 2.78/1.01      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.78/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 2.78/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2769,plain,
% 2.78/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 2.78/1.01      | sK1 = k1_xboole_0
% 2.78/1.01      | r1_tarski(X0,sK0) != iProver_top
% 2.78/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2603,c_1849]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_33,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.01      | ~ v1_relat_1(X1)
% 2.78/1.01      | v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2090,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | v1_relat_1(X0)
% 2.78/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2321,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.78/1.01      | v1_relat_1(sK3) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2090]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2322,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.78/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_7,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2564,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2565,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2774,plain,
% 2.78/1.01      ( r1_tarski(X0,sK0) != iProver_top
% 2.78/1.01      | sK1 = k1_xboole_0
% 2.78/1.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_2769,c_33,c_2322,c_2565]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2775,plain,
% 2.78/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 2.78/1.01      | sK1 = k1_xboole_0
% 2.78/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_2774]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2783,plain,
% 2.78/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1843,c_2775]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_22,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.78/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1844,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 2.78/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.78/1.01      | v1_funct_1(X0) != iProver_top
% 2.78/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4616,plain,
% 2.78/1.01      ( sK1 = k1_xboole_0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 2.78/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 2.78/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 2.78/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2783,c_1844]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_21,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.78/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1845,plain,
% 2.78/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 2.78/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.78/1.01      | v1_funct_1(X2) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3269,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 2.78/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1842,c_1845]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_30,negated_conjecture,
% 2.78/1.01      ( v1_funct_1(sK3) ),
% 2.78/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2169,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.01      | ~ v1_funct_1(sK3)
% 2.78/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2297,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.01      | ~ v1_funct_1(sK3)
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2169]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3364,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_3269,c_30,c_28,c_2297]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_19,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v1_funct_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1847,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.78/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4041,plain,
% 2.78/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 2.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_3364,c_1847]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_31,plain,
% 2.78/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4210,plain,
% 2.78/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4041,c_31,c_33]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1851,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.01      | v1_relat_1(X1) != iProver_top
% 2.78/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4218,plain,
% 2.78/1.01      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 2.78/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4210,c_1851]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4346,plain,
% 2.78/1.01      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4218,c_2565]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_20,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1846,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.01      | v1_funct_1(X0) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3169,plain,
% 2.78/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 2.78/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1842,c_1846]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2149,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.01      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 2.78/1.01      | ~ v1_funct_1(sK3) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2520,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 2.78/1.01      | ~ v1_funct_1(sK3) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2149]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2521,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 2.78/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3356,plain,
% 2.78/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_3169,c_31,c_33,c_2521]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3373,plain,
% 2.78/1.01      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_3364,c_3356]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5411,plain,
% 2.78/1.01      ( sK1 = k1_xboole_0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 2.78/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4616,c_4346,c_3373]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_23,plain,
% 2.78/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.78/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_25,negated_conjecture,
% 2.78/1.01      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 2.78/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_702,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 2.78/1.01      | k1_relat_1(X0) != sK2
% 2.78/1.01      | sK1 != X1 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_703,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_702]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_10,plain,
% 2.78/1.01      ( v5_relat_1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_6,plain,
% 2.78/1.01      ( ~ v5_relat_1(X0,X1)
% 2.78/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 2.78/1.01      | ~ v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_319,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 2.78/1.01      | ~ v1_relat_1(X0) ),
% 2.78/1.01      inference(resolution,[status(thm)],[c_10,c_6]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_715,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_703,c_319]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1830,plain,
% 2.78/1.01      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_720,plain,
% 2.78/1.01      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2275,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | ~ v1_funct_1(sK3) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2149]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2276,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 2.78/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2275]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2303,plain,
% 2.78/1.01      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 2.78/1.01      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_1830,c_31,c_33,c_720,c_2276]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2304,plain,
% 2.78/1.01      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_2303]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3370,plain,
% 2.78/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_3364,c_2304]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3502,plain,
% 2.78/1.01      ( sK1 = k1_xboole_0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2783,c_3370]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5422,plain,
% 2.78/1.01      ( sK1 = k1_xboole_0
% 2.78/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 2.78/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_5411,c_3502]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1839,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.78/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4221,plain,
% 2.78/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 2.78/1.01      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4210,c_1839]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4447,plain,
% 2.78/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4221,c_2565,c_4218]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5566,plain,
% 2.78/1.01      ( sK1 = k1_xboole_0 ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_5422,c_4346,c_4447]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_26,negated_conjecture,
% 2.78/1.01      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5586,plain,
% 2.78/1.01      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5566,c_26]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5587,plain,
% 2.78/1.01      ( sK0 = k1_xboole_0 ),
% 2.78/1.01      inference(equality_resolution_simp,[status(thm)],[c_5586]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_11,plain,
% 2.78/1.01      ( v4_relat_1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_8,plain,
% 2.78/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_301,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.78/1.01      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1840,plain,
% 2.78/1.01      ( k7_relat_1(X0,X1) = X0
% 2.78/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2908,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1842,c_1840]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2932,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK0) = sK3 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_2908,c_33,c_2322,c_2565]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5740,plain,
% 2.78/1.01      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5587,c_2932]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5573,plain,
% 2.78/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5566,c_4210]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5641,plain,
% 2.78/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_5573,c_5587]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2,plain,
% 2.78/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5643,plain,
% 2.78/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5641,c_2]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_721,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0
% 2.78/1.01      | sK1 != sK1 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1054,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0 ),
% 2.78/1.01      inference(equality_resolution_simp,[status(thm)],[c_721]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1829,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3371,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_3364,c_1829]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3388,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_3371,c_3373]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5575,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 2.78/1.01      | sK2 != sK0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5566,c_3388]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_13,plain,
% 2.78/1.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.78/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.78/1.01      | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_518,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK2 != X0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_519,plain,
% 2.78/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.78/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.78/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = sK2 ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_518]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1838,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = sK2
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1,plain,
% 2.78/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2008,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK2 = k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.78/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_1838,c_1]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2419,plain,
% 2.78/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | sK2 = k1_xboole_0
% 2.78/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_2008,c_31,c_33,c_2276]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2420,plain,
% 2.78/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK2 = k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_2419]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3369,plain,
% 2.78/1.01      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 2.78/1.01      | sK2 = k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_3364,c_2420]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_0,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_338,plain,
% 2.78/1.01      ( sK2 != X0 | sK0 != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_339,plain,
% 2.78/1.01      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK2 ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_338]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1415,plain,( X0 = X0 ),theory(equality) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2219,plain,
% 2.78/1.01      ( sK2 = sK2 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1415]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1416,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2116,plain,
% 2.78/1.01      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2369,plain,
% 2.78/1.01      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2116]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_14,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.78/1.01      | k1_xboole_0 = X1
% 2.78/1.01      | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_570,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.78/1.01      | sK3 != X0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | sK0 != X1
% 2.78/1.01      | k1_xboole_0 = X0
% 2.78/1.01      | k1_xboole_0 = X1 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_571,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = sK3
% 2.78/1.01      | k1_xboole_0 = sK0 ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_570]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1836,plain,
% 2.78/1.01      ( sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = sK3
% 2.78/1.01      | k1_xboole_0 = sK0
% 2.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1912,plain,
% 2.78/1.01      ( sK3 = k1_xboole_0
% 2.78/1.01      | sK1 != k1_xboole_0
% 2.78/1.01      | sK0 = k1_xboole_0
% 2.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_1836,c_1]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3,plain,
% 2.78/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = X0
% 2.78/1.01      | k1_xboole_0 = X1 ),
% 2.78/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_95,plain,
% 2.78/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_96,plain,
% 2.78/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2114,plain,
% 2.78/1.01      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2360,plain,
% 2.78/1.01      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2114]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2361,plain,
% 2.78/1.01      ( sK0 = sK0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1415]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2442,plain,
% 2.78/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2443,plain,
% 2.78/1.01      ( sK1 != k1_xboole_0
% 2.78/1.01      | k1_xboole_0 = sK1
% 2.78/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2442]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2516,plain,
% 2.78/1.01      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_1912,c_26,c_95,c_96,c_2360,c_2361,c_2443]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2517,plain,
% 2.78/1.01      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_2516]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3631,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_3369,c_339,c_2219,c_2369,c_2517]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5577,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5566,c_3631]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5614,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0 ),
% 2.78/1.01      inference(equality_resolution_simp,[status(thm)],[c_5577]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5632,plain,
% 2.78/1.01      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 2.78/1.01      | k1_xboole_0 != k1_xboole_0
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_5575,c_5587,c_5614]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5633,plain,
% 2.78/1.01      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.78/1.01      inference(equality_resolution_simp,[status(thm)],[c_5632]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5636,plain,
% 2.78/1.01      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 2.78/1.01      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_5633,c_2]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5645,plain,
% 2.78/1.01      ( k7_relat_1(sK3,k1_xboole_0) != sK3 ),
% 2.78/1.01      inference(backward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_5643,c_5636]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(contradiction,plain,
% 2.78/1.01      ( $false ),
% 2.78/1.01      inference(minisat,[status(thm)],[c_5740,c_5645]) ).
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  ------                               Statistics
% 2.78/1.01  
% 2.78/1.01  ------ General
% 2.78/1.01  
% 2.78/1.01  abstr_ref_over_cycles:                  0
% 2.78/1.01  abstr_ref_under_cycles:                 0
% 2.78/1.01  gc_basic_clause_elim:                   0
% 2.78/1.01  forced_gc_time:                         0
% 2.78/1.01  parsing_time:                           0.009
% 2.78/1.01  unif_index_cands_time:                  0.
% 2.78/1.01  unif_index_add_time:                    0.
% 2.78/1.01  orderings_time:                         0.
% 2.78/1.01  out_proof_time:                         0.013
% 2.78/1.01  total_time:                             0.149
% 2.78/1.01  num_of_symbols:                         50
% 2.78/1.01  num_of_terms:                           4532
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing
% 2.78/1.01  
% 2.78/1.01  num_of_splits:                          0
% 2.78/1.01  num_of_split_atoms:                     0
% 2.78/1.01  num_of_reused_defs:                     0
% 2.78/1.01  num_eq_ax_congr_red:                    15
% 2.78/1.01  num_of_sem_filtered_clauses:            1
% 2.78/1.01  num_of_subtypes:                        0
% 2.78/1.01  monotx_restored_types:                  0
% 2.78/1.01  sat_num_of_epr_types:                   0
% 2.78/1.01  sat_num_of_non_cyclic_types:            0
% 2.78/1.01  sat_guarded_non_collapsed_types:        0
% 2.78/1.01  num_pure_diseq_elim:                    0
% 2.78/1.01  simp_replaced_by:                       0
% 2.78/1.01  res_preprocessed:                       140
% 2.78/1.01  prep_upred:                             0
% 2.78/1.01  prep_unflattend:                        75
% 2.78/1.01  smt_new_axioms:                         0
% 2.78/1.01  pred_elim_cands:                        4
% 2.78/1.01  pred_elim:                              3
% 2.78/1.01  pred_elim_cl:                           1
% 2.78/1.01  pred_elim_cycles:                       6
% 2.78/1.01  merged_defs:                            0
% 2.78/1.01  merged_defs_ncl:                        0
% 2.78/1.01  bin_hyper_res:                          0
% 2.78/1.01  prep_cycles:                            4
% 2.78/1.01  pred_elim_time:                         0.013
% 2.78/1.01  splitting_time:                         0.
% 2.78/1.01  sem_filter_time:                        0.
% 2.78/1.01  monotx_time:                            0.
% 2.78/1.01  subtype_inf_time:                       0.
% 2.78/1.01  
% 2.78/1.01  ------ Problem properties
% 2.78/1.01  
% 2.78/1.01  clauses:                                29
% 2.78/1.01  conjectures:                            4
% 2.78/1.01  epr:                                    4
% 2.78/1.01  horn:                                   24
% 2.78/1.01  ground:                                 12
% 2.78/1.01  unary:                                  6
% 2.78/1.01  binary:                                 4
% 2.78/1.01  lits:                                   87
% 2.78/1.01  lits_eq:                                35
% 2.78/1.01  fd_pure:                                0
% 2.78/1.01  fd_pseudo:                              0
% 2.78/1.01  fd_cond:                                4
% 2.78/1.01  fd_pseudo_cond:                         0
% 2.78/1.01  ac_symbols:                             0
% 2.78/1.01  
% 2.78/1.01  ------ Propositional Solver
% 2.78/1.01  
% 2.78/1.01  prop_solver_calls:                      27
% 2.78/1.01  prop_fast_solver_calls:                 1256
% 2.78/1.01  smt_solver_calls:                       0
% 2.78/1.01  smt_fast_solver_calls:                  0
% 2.78/1.01  prop_num_of_clauses:                    1831
% 2.78/1.01  prop_preprocess_simplified:             5377
% 2.78/1.01  prop_fo_subsumed:                       30
% 2.78/1.01  prop_solver_time:                       0.
% 2.78/1.01  smt_solver_time:                        0.
% 2.78/1.01  smt_fast_solver_time:                   0.
% 2.78/1.01  prop_fast_solver_time:                  0.
% 2.78/1.01  prop_unsat_core_time:                   0.
% 2.78/1.01  
% 2.78/1.01  ------ QBF
% 2.78/1.01  
% 2.78/1.01  qbf_q_res:                              0
% 2.78/1.01  qbf_num_tautologies:                    0
% 2.78/1.01  qbf_prep_cycles:                        0
% 2.78/1.01  
% 2.78/1.01  ------ BMC1
% 2.78/1.01  
% 2.78/1.01  bmc1_current_bound:                     -1
% 2.78/1.01  bmc1_last_solved_bound:                 -1
% 2.78/1.01  bmc1_unsat_core_size:                   -1
% 2.78/1.01  bmc1_unsat_core_parents_size:           -1
% 2.78/1.01  bmc1_merge_next_fun:                    0
% 2.78/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation
% 2.78/1.01  
% 2.78/1.01  inst_num_of_clauses:                    547
% 2.78/1.01  inst_num_in_passive:                    36
% 2.78/1.01  inst_num_in_active:                     308
% 2.78/1.01  inst_num_in_unprocessed:                203
% 2.78/1.01  inst_num_of_loops:                      360
% 2.78/1.01  inst_num_of_learning_restarts:          0
% 2.78/1.01  inst_num_moves_active_passive:          49
% 2.78/1.01  inst_lit_activity:                      0
% 2.78/1.01  inst_lit_activity_moves:                0
% 2.78/1.01  inst_num_tautologies:                   0
% 2.78/1.01  inst_num_prop_implied:                  0
% 2.78/1.01  inst_num_existing_simplified:           0
% 2.78/1.01  inst_num_eq_res_simplified:             0
% 2.78/1.01  inst_num_child_elim:                    0
% 2.78/1.01  inst_num_of_dismatching_blockings:      95
% 2.78/1.01  inst_num_of_non_proper_insts:           450
% 2.78/1.01  inst_num_of_duplicates:                 0
% 2.78/1.01  inst_inst_num_from_inst_to_res:         0
% 2.78/1.01  inst_dismatching_checking_time:         0.
% 2.78/1.01  
% 2.78/1.01  ------ Resolution
% 2.78/1.01  
% 2.78/1.01  res_num_of_clauses:                     0
% 2.78/1.01  res_num_in_passive:                     0
% 2.78/1.01  res_num_in_active:                      0
% 2.78/1.01  res_num_of_loops:                       144
% 2.78/1.01  res_forward_subset_subsumed:            13
% 2.78/1.01  res_backward_subset_subsumed:           0
% 2.78/1.01  res_forward_subsumed:                   0
% 2.78/1.01  res_backward_subsumed:                  0
% 2.78/1.01  res_forward_subsumption_resolution:     3
% 2.78/1.01  res_backward_subsumption_resolution:    0
% 2.78/1.01  res_clause_to_clause_subsumption:       269
% 2.78/1.01  res_orphan_elimination:                 0
% 2.78/1.01  res_tautology_del:                      47
% 2.78/1.01  res_num_eq_res_simplified:              1
% 2.78/1.01  res_num_sel_changes:                    0
% 2.78/1.01  res_moves_from_active_to_pass:          0
% 2.78/1.01  
% 2.78/1.01  ------ Superposition
% 2.78/1.01  
% 2.78/1.01  sup_time_total:                         0.
% 2.78/1.01  sup_time_generating:                    0.
% 2.78/1.01  sup_time_sim_full:                      0.
% 2.78/1.01  sup_time_sim_immed:                     0.
% 2.78/1.01  
% 2.78/1.01  sup_num_of_clauses:                     84
% 2.78/1.01  sup_num_in_active:                      35
% 2.78/1.01  sup_num_in_passive:                     49
% 2.78/1.01  sup_num_of_loops:                       70
% 2.78/1.01  sup_fw_superposition:                   42
% 2.78/1.01  sup_bw_superposition:                   51
% 2.78/1.01  sup_immediate_simplified:               33
% 2.78/1.01  sup_given_eliminated:                   0
% 2.78/1.01  comparisons_done:                       0
% 2.78/1.01  comparisons_avoided:                    13
% 2.78/1.01  
% 2.78/1.01  ------ Simplifications
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  sim_fw_subset_subsumed:                 5
% 2.78/1.01  sim_bw_subset_subsumed:                 9
% 2.78/1.01  sim_fw_subsumed:                        2
% 2.78/1.01  sim_bw_subsumed:                        1
% 2.78/1.01  sim_fw_subsumption_res:                 9
% 2.78/1.01  sim_bw_subsumption_res:                 3
% 2.78/1.01  sim_tautology_del:                      4
% 2.78/1.01  sim_eq_tautology_del:                   8
% 2.78/1.01  sim_eq_res_simp:                        6
% 2.78/1.01  sim_fw_demodulated:                     11
% 2.78/1.01  sim_bw_demodulated:                     33
% 2.78/1.01  sim_light_normalised:                   13
% 2.78/1.01  sim_joinable_taut:                      0
% 2.78/1.01  sim_joinable_simp:                      0
% 2.78/1.01  sim_ac_normalised:                      0
% 2.78/1.01  sim_smt_subsumption:                    0
% 2.78/1.01  
%------------------------------------------------------------------------------
