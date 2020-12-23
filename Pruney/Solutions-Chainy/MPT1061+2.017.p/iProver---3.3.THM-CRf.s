%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:32 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  175 (1192 expanded)
%              Number of clauses        :  107 ( 432 expanded)
%              Number of leaves         :   18 ( 263 expanded)
%              Depth                    :   25
%              Number of atoms          :  530 (6559 expanded)
%              Number of equality atoms :  208 ( 666 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK4,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK4,X0,X3)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f40,f44,f43])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1184,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1178,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1187,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1688,plain,
    ( v4_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1187])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1192,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3021,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1192])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1431,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1432,plain,
    ( v4_relat_1(sK4,sK0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1431])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1613,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_1614,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1613])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1937,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1938,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_1877,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X0)
    | ~ v4_relat_1(sK4,X1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2178,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X0)
    | ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_2179,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top
    | v4_relat_1(sK4,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2178])).

cnf(c_3288,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_36,c_1432,c_1614,c_1938,c_2179])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1179,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_29])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1186,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1736,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1178,c_1186])).

cnf(c_1855,plain,
    ( k1_relat_1(sK4) = sK0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_1736])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_350,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_32])).

cnf(c_1928,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_350])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1188,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2896,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1928,c_1188])).

cnf(c_3312,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2896,c_36,c_1614,c_1938])).

cnf(c_3313,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3312])).

cnf(c_3321,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1179,c_3313])).

cnf(c_3,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1194,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3397,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_1194])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1191,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2197,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1191])).

cnf(c_1880,plain,
    ( ~ v4_relat_1(sK4,X0)
    | v1_relat_1(k7_relat_1(sK4,X1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2162,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | v1_relat_1(k7_relat_1(sK4,X0))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2163,plain,
    ( v4_relat_1(sK4,sK0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_2489,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2197,c_36,c_1432,c_1614,c_1938,c_2163])).

cnf(c_3498,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3397,c_2489])).

cnf(c_3503,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3288,c_3498])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1185,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2191,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1178,c_1185])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1180,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2320,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2191,c_1180])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2106,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1196])).

cnf(c_2337,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2106,c_36,c_1614,c_1938])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1189,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2342,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2337,c_1189])).

cnf(c_3736,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1184,c_1186])).

cnf(c_10279,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
    | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2342,c_3736])).

cnf(c_10367,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
    | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10279,c_2489])).

cnf(c_10372,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_10367])).

cnf(c_10400,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10372,c_3321])).

cnf(c_10508,plain,
    ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_10400])).

cnf(c_10516,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3503,c_10508])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1181,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2887,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1181])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1590,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_3132,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2887,c_31,c_29,c_1590])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1172,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_3139,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3132,c_1172])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3091,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1182])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1585,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1586,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1585])).

cnf(c_3096,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3091,c_34,c_36,c_1586])).

cnf(c_3140,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3132,c_3096])).

cnf(c_3146,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3139,c_3140])).

cnf(c_10954,plain,
    ( sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10516,c_3146])).

cnf(c_11102,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10954])).

cnf(c_11105,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1184,c_11102])).

cnf(c_11106,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11105,c_3321])).

cnf(c_11107,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11106,c_2342])).

cnf(c_8363,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_8364,plain,
    ( v4_relat_1(sK4,sK0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8363])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11107,c_8364,c_3503,c_2320,c_1938,c_1614,c_1432,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.69/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.04  
% 2.69/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.04  
% 2.69/1.04  ------  iProver source info
% 2.69/1.04  
% 2.69/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.04  git: non_committed_changes: false
% 2.69/1.04  git: last_make_outside_of_git: false
% 2.69/1.04  
% 2.69/1.04  ------ 
% 2.69/1.04  
% 2.69/1.04  ------ Input Options
% 2.69/1.04  
% 2.69/1.04  --out_options                           all
% 2.69/1.04  --tptp_safe_out                         true
% 2.69/1.04  --problem_path                          ""
% 2.69/1.04  --include_path                          ""
% 2.69/1.04  --clausifier                            res/vclausify_rel
% 2.69/1.04  --clausifier_options                    --mode clausify
% 2.69/1.04  --stdin                                 false
% 2.69/1.04  --stats_out                             all
% 2.69/1.04  
% 2.69/1.04  ------ General Options
% 2.69/1.04  
% 2.69/1.04  --fof                                   false
% 2.69/1.04  --time_out_real                         305.
% 2.69/1.04  --time_out_virtual                      -1.
% 2.69/1.04  --symbol_type_check                     false
% 2.69/1.04  --clausify_out                          false
% 2.69/1.04  --sig_cnt_out                           false
% 2.69/1.04  --trig_cnt_out                          false
% 2.69/1.04  --trig_cnt_out_tolerance                1.
% 2.69/1.04  --trig_cnt_out_sk_spl                   false
% 2.69/1.04  --abstr_cl_out                          false
% 2.69/1.04  
% 2.69/1.04  ------ Global Options
% 2.69/1.04  
% 2.69/1.04  --schedule                              default
% 2.69/1.04  --add_important_lit                     false
% 2.69/1.04  --prop_solver_per_cl                    1000
% 2.69/1.04  --min_unsat_core                        false
% 2.69/1.04  --soft_assumptions                      false
% 2.69/1.04  --soft_lemma_size                       3
% 2.69/1.04  --prop_impl_unit_size                   0
% 2.69/1.04  --prop_impl_unit                        []
% 2.69/1.04  --share_sel_clauses                     true
% 2.69/1.04  --reset_solvers                         false
% 2.69/1.04  --bc_imp_inh                            [conj_cone]
% 2.69/1.04  --conj_cone_tolerance                   3.
% 2.69/1.04  --extra_neg_conj                        none
% 2.69/1.04  --large_theory_mode                     true
% 2.69/1.04  --prolific_symb_bound                   200
% 2.69/1.04  --lt_threshold                          2000
% 2.69/1.04  --clause_weak_htbl                      true
% 2.69/1.04  --gc_record_bc_elim                     false
% 2.69/1.04  
% 2.69/1.04  ------ Preprocessing Options
% 2.69/1.04  
% 2.69/1.04  --preprocessing_flag                    true
% 2.69/1.04  --time_out_prep_mult                    0.1
% 2.69/1.04  --splitting_mode                        input
% 2.69/1.04  --splitting_grd                         true
% 2.69/1.04  --splitting_cvd                         false
% 2.69/1.04  --splitting_cvd_svl                     false
% 2.69/1.04  --splitting_nvd                         32
% 2.69/1.04  --sub_typing                            true
% 2.69/1.04  --prep_gs_sim                           true
% 2.69/1.04  --prep_unflatten                        true
% 2.69/1.04  --prep_res_sim                          true
% 2.69/1.04  --prep_upred                            true
% 2.69/1.04  --prep_sem_filter                       exhaustive
% 2.69/1.04  --prep_sem_filter_out                   false
% 2.69/1.04  --pred_elim                             true
% 2.69/1.04  --res_sim_input                         true
% 2.69/1.04  --eq_ax_congr_red                       true
% 2.69/1.04  --pure_diseq_elim                       true
% 2.69/1.04  --brand_transform                       false
% 2.69/1.04  --non_eq_to_eq                          false
% 2.69/1.04  --prep_def_merge                        true
% 2.69/1.04  --prep_def_merge_prop_impl              false
% 2.69/1.04  --prep_def_merge_mbd                    true
% 2.69/1.04  --prep_def_merge_tr_red                 false
% 2.69/1.04  --prep_def_merge_tr_cl                  false
% 2.69/1.04  --smt_preprocessing                     true
% 2.69/1.04  --smt_ac_axioms                         fast
% 2.69/1.04  --preprocessed_out                      false
% 2.69/1.04  --preprocessed_stats                    false
% 2.69/1.04  
% 2.69/1.04  ------ Abstraction refinement Options
% 2.69/1.04  
% 2.69/1.04  --abstr_ref                             []
% 2.69/1.04  --abstr_ref_prep                        false
% 2.69/1.04  --abstr_ref_until_sat                   false
% 2.69/1.04  --abstr_ref_sig_restrict                funpre
% 2.69/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.04  --abstr_ref_under                       []
% 2.69/1.04  
% 2.69/1.04  ------ SAT Options
% 2.69/1.04  
% 2.69/1.04  --sat_mode                              false
% 2.69/1.04  --sat_fm_restart_options                ""
% 2.69/1.04  --sat_gr_def                            false
% 2.69/1.04  --sat_epr_types                         true
% 2.69/1.04  --sat_non_cyclic_types                  false
% 2.69/1.04  --sat_finite_models                     false
% 2.69/1.04  --sat_fm_lemmas                         false
% 2.69/1.04  --sat_fm_prep                           false
% 2.69/1.04  --sat_fm_uc_incr                        true
% 2.69/1.04  --sat_out_model                         small
% 2.69/1.04  --sat_out_clauses                       false
% 2.69/1.04  
% 2.69/1.04  ------ QBF Options
% 2.69/1.04  
% 2.69/1.04  --qbf_mode                              false
% 2.69/1.04  --qbf_elim_univ                         false
% 2.69/1.04  --qbf_dom_inst                          none
% 2.69/1.04  --qbf_dom_pre_inst                      false
% 2.69/1.04  --qbf_sk_in                             false
% 2.69/1.04  --qbf_pred_elim                         true
% 2.69/1.04  --qbf_split                             512
% 2.69/1.04  
% 2.69/1.04  ------ BMC1 Options
% 2.69/1.04  
% 2.69/1.04  --bmc1_incremental                      false
% 2.69/1.04  --bmc1_axioms                           reachable_all
% 2.69/1.04  --bmc1_min_bound                        0
% 2.69/1.04  --bmc1_max_bound                        -1
% 2.69/1.04  --bmc1_max_bound_default                -1
% 2.69/1.04  --bmc1_symbol_reachability              true
% 2.69/1.04  --bmc1_property_lemmas                  false
% 2.69/1.04  --bmc1_k_induction                      false
% 2.69/1.04  --bmc1_non_equiv_states                 false
% 2.69/1.04  --bmc1_deadlock                         false
% 2.69/1.04  --bmc1_ucm                              false
% 2.69/1.04  --bmc1_add_unsat_core                   none
% 2.69/1.04  --bmc1_unsat_core_children              false
% 2.69/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.04  --bmc1_out_stat                         full
% 2.69/1.04  --bmc1_ground_init                      false
% 2.69/1.04  --bmc1_pre_inst_next_state              false
% 2.69/1.04  --bmc1_pre_inst_state                   false
% 2.69/1.04  --bmc1_pre_inst_reach_state             false
% 2.69/1.04  --bmc1_out_unsat_core                   false
% 2.69/1.04  --bmc1_aig_witness_out                  false
% 2.69/1.04  --bmc1_verbose                          false
% 2.69/1.04  --bmc1_dump_clauses_tptp                false
% 2.69/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.04  --bmc1_dump_file                        -
% 2.69/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.04  --bmc1_ucm_extend_mode                  1
% 2.69/1.04  --bmc1_ucm_init_mode                    2
% 2.69/1.04  --bmc1_ucm_cone_mode                    none
% 2.69/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.04  --bmc1_ucm_relax_model                  4
% 2.69/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.04  --bmc1_ucm_layered_model                none
% 2.69/1.04  --bmc1_ucm_max_lemma_size               10
% 2.69/1.04  
% 2.69/1.04  ------ AIG Options
% 2.69/1.04  
% 2.69/1.04  --aig_mode                              false
% 2.69/1.04  
% 2.69/1.04  ------ Instantiation Options
% 2.69/1.04  
% 2.69/1.04  --instantiation_flag                    true
% 2.69/1.04  --inst_sos_flag                         false
% 2.69/1.04  --inst_sos_phase                        true
% 2.69/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.04  --inst_lit_sel_side                     num_symb
% 2.69/1.04  --inst_solver_per_active                1400
% 2.69/1.04  --inst_solver_calls_frac                1.
% 2.69/1.04  --inst_passive_queue_type               priority_queues
% 2.69/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.04  --inst_passive_queues_freq              [25;2]
% 2.69/1.04  --inst_dismatching                      true
% 2.69/1.04  --inst_eager_unprocessed_to_passive     true
% 2.69/1.04  --inst_prop_sim_given                   true
% 2.69/1.04  --inst_prop_sim_new                     false
% 2.69/1.04  --inst_subs_new                         false
% 2.69/1.04  --inst_eq_res_simp                      false
% 2.69/1.04  --inst_subs_given                       false
% 2.69/1.04  --inst_orphan_elimination               true
% 2.69/1.04  --inst_learning_loop_flag               true
% 2.69/1.04  --inst_learning_start                   3000
% 2.69/1.04  --inst_learning_factor                  2
% 2.69/1.04  --inst_start_prop_sim_after_learn       3
% 2.69/1.04  --inst_sel_renew                        solver
% 2.69/1.04  --inst_lit_activity_flag                true
% 2.69/1.04  --inst_restr_to_given                   false
% 2.69/1.04  --inst_activity_threshold               500
% 2.69/1.04  --inst_out_proof                        true
% 2.69/1.04  
% 2.69/1.04  ------ Resolution Options
% 2.69/1.04  
% 2.69/1.04  --resolution_flag                       true
% 2.69/1.04  --res_lit_sel                           adaptive
% 2.69/1.04  --res_lit_sel_side                      none
% 2.69/1.04  --res_ordering                          kbo
% 2.69/1.04  --res_to_prop_solver                    active
% 2.69/1.04  --res_prop_simpl_new                    false
% 2.69/1.04  --res_prop_simpl_given                  true
% 2.69/1.04  --res_passive_queue_type                priority_queues
% 2.69/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.04  --res_passive_queues_freq               [15;5]
% 2.69/1.04  --res_forward_subs                      full
% 2.69/1.04  --res_backward_subs                     full
% 2.69/1.04  --res_forward_subs_resolution           true
% 2.69/1.04  --res_backward_subs_resolution          true
% 2.69/1.04  --res_orphan_elimination                true
% 2.69/1.04  --res_time_limit                        2.
% 2.69/1.04  --res_out_proof                         true
% 2.69/1.04  
% 2.69/1.04  ------ Superposition Options
% 2.69/1.04  
% 2.69/1.04  --superposition_flag                    true
% 2.69/1.04  --sup_passive_queue_type                priority_queues
% 2.69/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.04  --demod_completeness_check              fast
% 2.69/1.04  --demod_use_ground                      true
% 2.69/1.04  --sup_to_prop_solver                    passive
% 2.69/1.04  --sup_prop_simpl_new                    true
% 2.69/1.04  --sup_prop_simpl_given                  true
% 2.69/1.04  --sup_fun_splitting                     false
% 2.69/1.04  --sup_smt_interval                      50000
% 2.69/1.04  
% 2.69/1.04  ------ Superposition Simplification Setup
% 2.69/1.04  
% 2.69/1.04  --sup_indices_passive                   []
% 2.69/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_full_bw                           [BwDemod]
% 2.69/1.04  --sup_immed_triv                        [TrivRules]
% 2.69/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_immed_bw_main                     []
% 2.69/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.04  
% 2.69/1.04  ------ Combination Options
% 2.69/1.04  
% 2.69/1.04  --comb_res_mult                         3
% 2.69/1.04  --comb_sup_mult                         2
% 2.69/1.04  --comb_inst_mult                        10
% 2.69/1.04  
% 2.69/1.04  ------ Debug Options
% 2.69/1.04  
% 2.69/1.04  --dbg_backtrace                         false
% 2.69/1.04  --dbg_dump_prop_clauses                 false
% 2.69/1.04  --dbg_dump_prop_clauses_file            -
% 2.69/1.04  --dbg_out_stat                          false
% 2.69/1.04  ------ Parsing...
% 2.69/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.04  
% 2.69/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.69/1.04  
% 2.69/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.04  
% 2.69/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.04  ------ Proving...
% 2.69/1.04  ------ Problem Properties 
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  clauses                                 28
% 2.69/1.04  conjectures                             4
% 2.69/1.04  EPR                                     3
% 2.69/1.04  Horn                                    26
% 2.69/1.04  unary                                   6
% 2.69/1.04  binary                                  5
% 2.69/1.04  lits                                    77
% 2.69/1.04  lits eq                                 22
% 2.69/1.04  fd_pure                                 0
% 2.69/1.04  fd_pseudo                               0
% 2.69/1.04  fd_cond                                 1
% 2.69/1.04  fd_pseudo_cond                          0
% 2.69/1.04  AC symbols                              0
% 2.69/1.04  
% 2.69/1.04  ------ Schedule dynamic 5 is on 
% 2.69/1.04  
% 2.69/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  ------ 
% 2.69/1.04  Current options:
% 2.69/1.04  ------ 
% 2.69/1.04  
% 2.69/1.04  ------ Input Options
% 2.69/1.04  
% 2.69/1.04  --out_options                           all
% 2.69/1.04  --tptp_safe_out                         true
% 2.69/1.04  --problem_path                          ""
% 2.69/1.04  --include_path                          ""
% 2.69/1.04  --clausifier                            res/vclausify_rel
% 2.69/1.04  --clausifier_options                    --mode clausify
% 2.69/1.04  --stdin                                 false
% 2.69/1.04  --stats_out                             all
% 2.69/1.04  
% 2.69/1.04  ------ General Options
% 2.69/1.04  
% 2.69/1.04  --fof                                   false
% 2.69/1.04  --time_out_real                         305.
% 2.69/1.04  --time_out_virtual                      -1.
% 2.69/1.04  --symbol_type_check                     false
% 2.69/1.04  --clausify_out                          false
% 2.69/1.04  --sig_cnt_out                           false
% 2.69/1.04  --trig_cnt_out                          false
% 2.69/1.04  --trig_cnt_out_tolerance                1.
% 2.69/1.04  --trig_cnt_out_sk_spl                   false
% 2.69/1.04  --abstr_cl_out                          false
% 2.69/1.04  
% 2.69/1.04  ------ Global Options
% 2.69/1.04  
% 2.69/1.04  --schedule                              default
% 2.69/1.04  --add_important_lit                     false
% 2.69/1.04  --prop_solver_per_cl                    1000
% 2.69/1.04  --min_unsat_core                        false
% 2.69/1.04  --soft_assumptions                      false
% 2.69/1.04  --soft_lemma_size                       3
% 2.69/1.04  --prop_impl_unit_size                   0
% 2.69/1.04  --prop_impl_unit                        []
% 2.69/1.04  --share_sel_clauses                     true
% 2.69/1.04  --reset_solvers                         false
% 2.69/1.04  --bc_imp_inh                            [conj_cone]
% 2.69/1.04  --conj_cone_tolerance                   3.
% 2.69/1.04  --extra_neg_conj                        none
% 2.69/1.04  --large_theory_mode                     true
% 2.69/1.04  --prolific_symb_bound                   200
% 2.69/1.04  --lt_threshold                          2000
% 2.69/1.04  --clause_weak_htbl                      true
% 2.69/1.04  --gc_record_bc_elim                     false
% 2.69/1.04  
% 2.69/1.04  ------ Preprocessing Options
% 2.69/1.04  
% 2.69/1.04  --preprocessing_flag                    true
% 2.69/1.04  --time_out_prep_mult                    0.1
% 2.69/1.04  --splitting_mode                        input
% 2.69/1.04  --splitting_grd                         true
% 2.69/1.04  --splitting_cvd                         false
% 2.69/1.04  --splitting_cvd_svl                     false
% 2.69/1.04  --splitting_nvd                         32
% 2.69/1.04  --sub_typing                            true
% 2.69/1.04  --prep_gs_sim                           true
% 2.69/1.04  --prep_unflatten                        true
% 2.69/1.04  --prep_res_sim                          true
% 2.69/1.04  --prep_upred                            true
% 2.69/1.04  --prep_sem_filter                       exhaustive
% 2.69/1.04  --prep_sem_filter_out                   false
% 2.69/1.04  --pred_elim                             true
% 2.69/1.04  --res_sim_input                         true
% 2.69/1.04  --eq_ax_congr_red                       true
% 2.69/1.04  --pure_diseq_elim                       true
% 2.69/1.04  --brand_transform                       false
% 2.69/1.04  --non_eq_to_eq                          false
% 2.69/1.04  --prep_def_merge                        true
% 2.69/1.04  --prep_def_merge_prop_impl              false
% 2.69/1.04  --prep_def_merge_mbd                    true
% 2.69/1.04  --prep_def_merge_tr_red                 false
% 2.69/1.04  --prep_def_merge_tr_cl                  false
% 2.69/1.04  --smt_preprocessing                     true
% 2.69/1.04  --smt_ac_axioms                         fast
% 2.69/1.04  --preprocessed_out                      false
% 2.69/1.04  --preprocessed_stats                    false
% 2.69/1.04  
% 2.69/1.04  ------ Abstraction refinement Options
% 2.69/1.04  
% 2.69/1.04  --abstr_ref                             []
% 2.69/1.04  --abstr_ref_prep                        false
% 2.69/1.04  --abstr_ref_until_sat                   false
% 2.69/1.04  --abstr_ref_sig_restrict                funpre
% 2.69/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.04  --abstr_ref_under                       []
% 2.69/1.04  
% 2.69/1.04  ------ SAT Options
% 2.69/1.04  
% 2.69/1.04  --sat_mode                              false
% 2.69/1.04  --sat_fm_restart_options                ""
% 2.69/1.04  --sat_gr_def                            false
% 2.69/1.04  --sat_epr_types                         true
% 2.69/1.04  --sat_non_cyclic_types                  false
% 2.69/1.04  --sat_finite_models                     false
% 2.69/1.04  --sat_fm_lemmas                         false
% 2.69/1.04  --sat_fm_prep                           false
% 2.69/1.04  --sat_fm_uc_incr                        true
% 2.69/1.04  --sat_out_model                         small
% 2.69/1.04  --sat_out_clauses                       false
% 2.69/1.04  
% 2.69/1.04  ------ QBF Options
% 2.69/1.04  
% 2.69/1.04  --qbf_mode                              false
% 2.69/1.04  --qbf_elim_univ                         false
% 2.69/1.04  --qbf_dom_inst                          none
% 2.69/1.04  --qbf_dom_pre_inst                      false
% 2.69/1.04  --qbf_sk_in                             false
% 2.69/1.04  --qbf_pred_elim                         true
% 2.69/1.04  --qbf_split                             512
% 2.69/1.04  
% 2.69/1.04  ------ BMC1 Options
% 2.69/1.04  
% 2.69/1.04  --bmc1_incremental                      false
% 2.69/1.04  --bmc1_axioms                           reachable_all
% 2.69/1.04  --bmc1_min_bound                        0
% 2.69/1.04  --bmc1_max_bound                        -1
% 2.69/1.04  --bmc1_max_bound_default                -1
% 2.69/1.04  --bmc1_symbol_reachability              true
% 2.69/1.04  --bmc1_property_lemmas                  false
% 2.69/1.04  --bmc1_k_induction                      false
% 2.69/1.04  --bmc1_non_equiv_states                 false
% 2.69/1.04  --bmc1_deadlock                         false
% 2.69/1.04  --bmc1_ucm                              false
% 2.69/1.04  --bmc1_add_unsat_core                   none
% 2.69/1.04  --bmc1_unsat_core_children              false
% 2.69/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.04  --bmc1_out_stat                         full
% 2.69/1.04  --bmc1_ground_init                      false
% 2.69/1.04  --bmc1_pre_inst_next_state              false
% 2.69/1.04  --bmc1_pre_inst_state                   false
% 2.69/1.04  --bmc1_pre_inst_reach_state             false
% 2.69/1.04  --bmc1_out_unsat_core                   false
% 2.69/1.04  --bmc1_aig_witness_out                  false
% 2.69/1.04  --bmc1_verbose                          false
% 2.69/1.04  --bmc1_dump_clauses_tptp                false
% 2.69/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.04  --bmc1_dump_file                        -
% 2.69/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.04  --bmc1_ucm_extend_mode                  1
% 2.69/1.04  --bmc1_ucm_init_mode                    2
% 2.69/1.04  --bmc1_ucm_cone_mode                    none
% 2.69/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.04  --bmc1_ucm_relax_model                  4
% 2.69/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.04  --bmc1_ucm_layered_model                none
% 2.69/1.04  --bmc1_ucm_max_lemma_size               10
% 2.69/1.04  
% 2.69/1.04  ------ AIG Options
% 2.69/1.04  
% 2.69/1.04  --aig_mode                              false
% 2.69/1.04  
% 2.69/1.04  ------ Instantiation Options
% 2.69/1.04  
% 2.69/1.04  --instantiation_flag                    true
% 2.69/1.04  --inst_sos_flag                         false
% 2.69/1.04  --inst_sos_phase                        true
% 2.69/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.04  --inst_lit_sel_side                     none
% 2.69/1.04  --inst_solver_per_active                1400
% 2.69/1.04  --inst_solver_calls_frac                1.
% 2.69/1.04  --inst_passive_queue_type               priority_queues
% 2.69/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.04  --inst_passive_queues_freq              [25;2]
% 2.69/1.04  --inst_dismatching                      true
% 2.69/1.04  --inst_eager_unprocessed_to_passive     true
% 2.69/1.04  --inst_prop_sim_given                   true
% 2.69/1.04  --inst_prop_sim_new                     false
% 2.69/1.04  --inst_subs_new                         false
% 2.69/1.04  --inst_eq_res_simp                      false
% 2.69/1.04  --inst_subs_given                       false
% 2.69/1.04  --inst_orphan_elimination               true
% 2.69/1.04  --inst_learning_loop_flag               true
% 2.69/1.04  --inst_learning_start                   3000
% 2.69/1.04  --inst_learning_factor                  2
% 2.69/1.04  --inst_start_prop_sim_after_learn       3
% 2.69/1.04  --inst_sel_renew                        solver
% 2.69/1.04  --inst_lit_activity_flag                true
% 2.69/1.04  --inst_restr_to_given                   false
% 2.69/1.04  --inst_activity_threshold               500
% 2.69/1.04  --inst_out_proof                        true
% 2.69/1.04  
% 2.69/1.04  ------ Resolution Options
% 2.69/1.04  
% 2.69/1.04  --resolution_flag                       false
% 2.69/1.04  --res_lit_sel                           adaptive
% 2.69/1.04  --res_lit_sel_side                      none
% 2.69/1.04  --res_ordering                          kbo
% 2.69/1.04  --res_to_prop_solver                    active
% 2.69/1.04  --res_prop_simpl_new                    false
% 2.69/1.04  --res_prop_simpl_given                  true
% 2.69/1.04  --res_passive_queue_type                priority_queues
% 2.69/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.04  --res_passive_queues_freq               [15;5]
% 2.69/1.04  --res_forward_subs                      full
% 2.69/1.04  --res_backward_subs                     full
% 2.69/1.04  --res_forward_subs_resolution           true
% 2.69/1.04  --res_backward_subs_resolution          true
% 2.69/1.04  --res_orphan_elimination                true
% 2.69/1.04  --res_time_limit                        2.
% 2.69/1.04  --res_out_proof                         true
% 2.69/1.04  
% 2.69/1.04  ------ Superposition Options
% 2.69/1.04  
% 2.69/1.04  --superposition_flag                    true
% 2.69/1.04  --sup_passive_queue_type                priority_queues
% 2.69/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.04  --demod_completeness_check              fast
% 2.69/1.04  --demod_use_ground                      true
% 2.69/1.04  --sup_to_prop_solver                    passive
% 2.69/1.04  --sup_prop_simpl_new                    true
% 2.69/1.04  --sup_prop_simpl_given                  true
% 2.69/1.04  --sup_fun_splitting                     false
% 2.69/1.04  --sup_smt_interval                      50000
% 2.69/1.04  
% 2.69/1.04  ------ Superposition Simplification Setup
% 2.69/1.04  
% 2.69/1.04  --sup_indices_passive                   []
% 2.69/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_full_bw                           [BwDemod]
% 2.69/1.04  --sup_immed_triv                        [TrivRules]
% 2.69/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_immed_bw_main                     []
% 2.69/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.04  
% 2.69/1.04  ------ Combination Options
% 2.69/1.04  
% 2.69/1.04  --comb_res_mult                         3
% 2.69/1.04  --comb_sup_mult                         2
% 2.69/1.04  --comb_inst_mult                        10
% 2.69/1.04  
% 2.69/1.04  ------ Debug Options
% 2.69/1.04  
% 2.69/1.04  --dbg_backtrace                         false
% 2.69/1.04  --dbg_dump_prop_clauses                 false
% 2.69/1.04  --dbg_dump_prop_clauses_file            -
% 2.69/1.04  --dbg_out_stat                          false
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  ------ Proving...
% 2.69/1.04  
% 2.69/1.04  
% 2.69/1.04  % SZS status Theorem for theBenchmark.p
% 2.69/1.04  
% 2.69/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.04  
% 2.69/1.04  fof(f11,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f29,plain,(
% 2.69/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.69/1.04    inference(ennf_transformation,[],[f11])).
% 2.69/1.04  
% 2.69/1.04  fof(f30,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.69/1.04    inference(flattening,[],[f29])).
% 2.69/1.04  
% 2.69/1.04  fof(f59,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f30])).
% 2.69/1.04  
% 2.69/1.04  fof(f16,conjecture,(
% 2.69/1.04    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f17,negated_conjecture,(
% 2.69/1.04    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.69/1.04    inference(negated_conjecture,[],[f16])).
% 2.69/1.04  
% 2.69/1.04  fof(f39,plain,(
% 2.69/1.04    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 2.69/1.04    inference(ennf_transformation,[],[f17])).
% 2.69/1.04  
% 2.69/1.04  fof(f40,plain,(
% 2.69/1.04    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 2.69/1.04    inference(flattening,[],[f39])).
% 2.69/1.04  
% 2.69/1.04  fof(f44,plain,(
% 2.69/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 2.69/1.04    introduced(choice_axiom,[])).
% 2.69/1.04  
% 2.69/1.04  fof(f43,plain,(
% 2.69/1.04    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 2.69/1.04    introduced(choice_axiom,[])).
% 2.69/1.04  
% 2.69/1.04  fof(f45,plain,(
% 2.69/1.04    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 2.69/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f40,f44,f43])).
% 2.69/1.04  
% 2.69/1.04  fof(f75,plain,(
% 2.69/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f8,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f18,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.69/1.04    inference(pure_predicate_removal,[],[f8])).
% 2.69/1.04  
% 2.69/1.04  fof(f26,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(ennf_transformation,[],[f18])).
% 2.69/1.04  
% 2.69/1.04  fof(f56,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.04    inference(cnf_transformation,[],[f26])).
% 2.69/1.04  
% 2.69/1.04  fof(f4,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f21,plain,(
% 2.69/1.04    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 2.69/1.04    inference(ennf_transformation,[],[f4])).
% 2.69/1.04  
% 2.69/1.04  fof(f22,plain,(
% 2.69/1.04    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 2.69/1.04    inference(flattening,[],[f21])).
% 2.69/1.04  
% 2.69/1.04  fof(f51,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f22])).
% 2.69/1.04  
% 2.69/1.04  fof(f2,axiom,(
% 2.69/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f19,plain,(
% 2.69/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.69/1.04    inference(ennf_transformation,[],[f2])).
% 2.69/1.04  
% 2.69/1.04  fof(f47,plain,(
% 2.69/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f19])).
% 2.69/1.04  
% 2.69/1.04  fof(f5,axiom,(
% 2.69/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f53,plain,(
% 2.69/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.69/1.04    inference(cnf_transformation,[],[f5])).
% 2.69/1.04  
% 2.69/1.04  fof(f76,plain,(
% 2.69/1.04    r1_tarski(sK1,sK0)),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f12,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f31,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(ennf_transformation,[],[f12])).
% 2.69/1.04  
% 2.69/1.04  fof(f32,plain,(
% 2.69/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(flattening,[],[f31])).
% 2.69/1.04  
% 2.69/1.04  fof(f42,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(nnf_transformation,[],[f32])).
% 2.69/1.04  
% 2.69/1.04  fof(f60,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.04    inference(cnf_transformation,[],[f42])).
% 2.69/1.04  
% 2.69/1.04  fof(f74,plain,(
% 2.69/1.04    v1_funct_2(sK4,sK0,sK3)),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f9,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f27,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(ennf_transformation,[],[f9])).
% 2.69/1.04  
% 2.69/1.04  fof(f57,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.04    inference(cnf_transformation,[],[f27])).
% 2.69/1.04  
% 2.69/1.04  fof(f1,axiom,(
% 2.69/1.04    v1_xboole_0(k1_xboole_0)),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f46,plain,(
% 2.69/1.04    v1_xboole_0(k1_xboole_0)),
% 2.69/1.04    inference(cnf_transformation,[],[f1])).
% 2.69/1.04  
% 2.69/1.04  fof(f72,plain,(
% 2.69/1.04    ~v1_xboole_0(sK3)),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f7,axiom,(
% 2.69/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f24,plain,(
% 2.69/1.04    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.69/1.04    inference(ennf_transformation,[],[f7])).
% 2.69/1.04  
% 2.69/1.04  fof(f25,plain,(
% 2.69/1.04    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.69/1.04    inference(flattening,[],[f24])).
% 2.69/1.04  
% 2.69/1.04  fof(f55,plain,(
% 2.69/1.04    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f25])).
% 2.69/1.04  
% 2.69/1.04  fof(f3,axiom,(
% 2.69/1.04    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f20,plain,(
% 2.69/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.69/1.04    inference(ennf_transformation,[],[f3])).
% 2.69/1.04  
% 2.69/1.04  fof(f41,plain,(
% 2.69/1.04    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.69/1.04    inference(nnf_transformation,[],[f20])).
% 2.69/1.04  
% 2.69/1.04  fof(f48,plain,(
% 2.69/1.04    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f41])).
% 2.69/1.04  
% 2.69/1.04  fof(f50,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f22])).
% 2.69/1.04  
% 2.69/1.04  fof(f10,axiom,(
% 2.69/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f28,plain,(
% 2.69/1.04    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.04    inference(ennf_transformation,[],[f10])).
% 2.69/1.04  
% 2.69/1.04  fof(f58,plain,(
% 2.69/1.04    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.04    inference(cnf_transformation,[],[f28])).
% 2.69/1.04  
% 2.69/1.04  fof(f77,plain,(
% 2.69/1.04    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f6,axiom,(
% 2.69/1.04    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f23,plain,(
% 2.69/1.04    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/1.04    inference(ennf_transformation,[],[f6])).
% 2.69/1.04  
% 2.69/1.04  fof(f54,plain,(
% 2.69/1.04    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f23])).
% 2.69/1.04  
% 2.69/1.04  fof(f14,axiom,(
% 2.69/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f35,plain,(
% 2.69/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.69/1.04    inference(ennf_transformation,[],[f14])).
% 2.69/1.04  
% 2.69/1.04  fof(f36,plain,(
% 2.69/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.69/1.04    inference(flattening,[],[f35])).
% 2.69/1.04  
% 2.69/1.04  fof(f68,plain,(
% 2.69/1.04    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f36])).
% 2.69/1.04  
% 2.69/1.04  fof(f73,plain,(
% 2.69/1.04    v1_funct_1(sK4)),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f15,axiom,(
% 2.69/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f37,plain,(
% 2.69/1.04    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.69/1.04    inference(ennf_transformation,[],[f15])).
% 2.69/1.04  
% 2.69/1.04  fof(f38,plain,(
% 2.69/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.69/1.04    inference(flattening,[],[f37])).
% 2.69/1.04  
% 2.69/1.04  fof(f70,plain,(
% 2.69/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f38])).
% 2.69/1.04  
% 2.69/1.04  fof(f78,plain,(
% 2.69/1.04    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 2.69/1.04    inference(cnf_transformation,[],[f45])).
% 2.69/1.04  
% 2.69/1.04  fof(f13,axiom,(
% 2.69/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.69/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.04  
% 2.69/1.04  fof(f33,plain,(
% 2.69/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.69/1.04    inference(ennf_transformation,[],[f13])).
% 2.69/1.04  
% 2.69/1.04  fof(f34,plain,(
% 2.69/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.69/1.04    inference(flattening,[],[f33])).
% 2.69/1.04  
% 2.69/1.04  fof(f66,plain,(
% 2.69/1.04    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.69/1.04    inference(cnf_transformation,[],[f34])).
% 2.69/1.04  
% 2.69/1.04  cnf(c_13,plain,
% 2.69/1.04      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.69/1.04      | ~ r1_tarski(k1_relat_1(X0),X2)
% 2.69/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.69/1.04      | ~ v1_relat_1(X0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1184,plain,
% 2.69/1.04      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.69/1.04      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 2.69/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 2.69/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_29,negated_conjecture,
% 2.69/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.69/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1178,plain,
% 2.69/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10,plain,
% 2.69/1.04      ( v4_relat_1(X0,X1)
% 2.69/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1187,plain,
% 2.69/1.04      ( v4_relat_1(X0,X1) = iProver_top
% 2.69/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1688,plain,
% 2.69/1.04      ( v4_relat_1(sK4,sK0) = iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1178,c_1187]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_5,plain,
% 2.69/1.04      ( ~ v4_relat_1(X0,X1)
% 2.69/1.04      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 2.69/1.04      | ~ v1_relat_1(X0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1192,plain,
% 2.69/1.04      ( v4_relat_1(X0,X1) != iProver_top
% 2.69/1.04      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 2.69/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3021,plain,
% 2.69/1.04      ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top
% 2.69/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1688,c_1192]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_36,plain,
% 2.69/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1431,plain,
% 2.69/1.04      ( v4_relat_1(sK4,sK0)
% 2.69/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1432,plain,
% 2.69/1.04      ( v4_relat_1(sK4,sK0) = iProver_top
% 2.69/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_1431]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1,plain,
% 2.69/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.04      | ~ v1_relat_1(X1)
% 2.69/1.04      | v1_relat_1(X0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f47]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1411,plain,
% 2.69/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.04      | v1_relat_1(X0)
% 2.69/1.04      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1613,plain,
% 2.69/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.69/1.04      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
% 2.69/1.04      | v1_relat_1(sK4) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_1411]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1614,plain,
% 2.69/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.69/1.04      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 2.69/1.04      | v1_relat_1(sK4) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_1613]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_7,plain,
% 2.69/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.69/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1937,plain,
% 2.69/1.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1938,plain,
% 2.69/1.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1877,plain,
% 2.69/1.04      ( v4_relat_1(k7_relat_1(sK4,X0),X0)
% 2.69/1.04      | ~ v4_relat_1(sK4,X1)
% 2.69/1.04      | ~ v1_relat_1(sK4) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2178,plain,
% 2.69/1.04      ( v4_relat_1(k7_relat_1(sK4,X0),X0)
% 2.69/1.04      | ~ v4_relat_1(sK4,sK0)
% 2.69/1.04      | ~ v1_relat_1(sK4) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_1877]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2179,plain,
% 2.69/1.04      ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top
% 2.69/1.04      | v4_relat_1(sK4,sK0) != iProver_top
% 2.69/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_2178]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3288,plain,
% 2.69/1.04      ( v4_relat_1(k7_relat_1(sK4,X0),X0) = iProver_top ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_3021,c_36,c_1432,c_1614,c_1938,c_2179]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_28,negated_conjecture,
% 2.69/1.04      ( r1_tarski(sK1,sK0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1179,plain,
% 2.69/1.04      ( r1_tarski(sK1,sK0) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_19,plain,
% 2.69/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.69/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.69/1.04      | k1_xboole_0 = X2 ),
% 2.69/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_30,negated_conjecture,
% 2.69/1.04      ( v1_funct_2(sK4,sK0,sK3) ),
% 2.69/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_466,plain,
% 2.69/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.69/1.04      | sK4 != X0
% 2.69/1.04      | sK3 != X2
% 2.69/1.04      | sK0 != X1
% 2.69/1.04      | k1_xboole_0 = X2 ),
% 2.69/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_467,plain,
% 2.69/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.69/1.04      | k1_relset_1(sK0,sK3,sK4) = sK0
% 2.69/1.04      | k1_xboole_0 = sK3 ),
% 2.69/1.04      inference(unflattening,[status(thm)],[c_466]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_469,plain,
% 2.69/1.04      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_467,c_29]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_11,plain,
% 2.69/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1186,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.69/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1736,plain,
% 2.69/1.04      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1178,c_1186]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1855,plain,
% 2.69/1.04      ( k1_relat_1(sK4) = sK0 | sK3 = k1_xboole_0 ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_469,c_1736]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_0,plain,
% 2.69/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f46]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_32,negated_conjecture,
% 2.69/1.04      ( ~ v1_xboole_0(sK3) ),
% 2.69/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_350,plain,
% 2.69/1.04      ( sK3 != k1_xboole_0 ),
% 2.69/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_32]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1928,plain,
% 2.69/1.04      ( k1_relat_1(sK4) = sK0 ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_1855,c_350]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_9,plain,
% 2.69/1.04      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.69/1.04      | ~ v1_relat_1(X1)
% 2.69/1.04      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.69/1.04      inference(cnf_transformation,[],[f55]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1188,plain,
% 2.69/1.04      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.69/1.04      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 2.69/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2896,plain,
% 2.69/1.04      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 2.69/1.04      | r1_tarski(X0,sK0) != iProver_top
% 2.69/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1928,c_1188]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3312,plain,
% 2.69/1.04      ( r1_tarski(X0,sK0) != iProver_top
% 2.69/1.04      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_2896,c_36,c_1614,c_1938]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3313,plain,
% 2.69/1.04      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 2.69/1.04      | r1_tarski(X0,sK0) != iProver_top ),
% 2.69/1.04      inference(renaming,[status(thm)],[c_3312]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3321,plain,
% 2.69/1.04      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1179,c_3313]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3,plain,
% 2.69/1.04      ( r1_tarski(k1_relat_1(X0),X1)
% 2.69/1.04      | ~ v4_relat_1(X0,X1)
% 2.69/1.04      | ~ v1_relat_1(X0) ),
% 2.69/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1194,plain,
% 2.69/1.04      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.69/1.04      | v4_relat_1(X0,X1) != iProver_top
% 2.69/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3397,plain,
% 2.69/1.04      ( r1_tarski(sK1,X0) = iProver_top
% 2.69/1.04      | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
% 2.69/1.04      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_3321,c_1194]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_6,plain,
% 2.69/1.04      ( ~ v4_relat_1(X0,X1)
% 2.69/1.04      | ~ v1_relat_1(X0)
% 2.69/1.04      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 2.69/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1191,plain,
% 2.69/1.04      ( v4_relat_1(X0,X1) != iProver_top
% 2.69/1.04      | v1_relat_1(X0) != iProver_top
% 2.69/1.04      | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2197,plain,
% 2.69/1.04      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 2.69/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1688,c_1191]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1880,plain,
% 2.69/1.04      ( ~ v4_relat_1(sK4,X0)
% 2.69/1.04      | v1_relat_1(k7_relat_1(sK4,X1))
% 2.69/1.04      | ~ v1_relat_1(sK4) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2162,plain,
% 2.69/1.04      ( ~ v4_relat_1(sK4,sK0)
% 2.69/1.04      | v1_relat_1(k7_relat_1(sK4,X0))
% 2.69/1.04      | ~ v1_relat_1(sK4) ),
% 2.69/1.04      inference(instantiation,[status(thm)],[c_1880]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2163,plain,
% 2.69/1.04      ( v4_relat_1(sK4,sK0) != iProver_top
% 2.69/1.04      | v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 2.69/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2489,plain,
% 2.69/1.04      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_2197,c_36,c_1432,c_1614,c_1938,c_2163]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3498,plain,
% 2.69/1.04      ( r1_tarski(sK1,X0) = iProver_top
% 2.69/1.04      | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top ),
% 2.69/1.04      inference(forward_subsumption_resolution,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_3397,c_2489]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3503,plain,
% 2.69/1.04      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_3288,c_3498]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_12,plain,
% 2.69/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.04      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.69/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1185,plain,
% 2.69/1.04      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.69/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2191,plain,
% 2.69/1.04      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1178,c_1185]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_27,negated_conjecture,
% 2.69/1.04      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 2.69/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1180,plain,
% 2.69/1.04      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2320,plain,
% 2.69/1.04      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 2.69/1.04      inference(demodulation,[status(thm)],[c_2191,c_1180]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1196,plain,
% 2.69/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.69/1.04      | v1_relat_1(X1) != iProver_top
% 2.69/1.04      | v1_relat_1(X0) = iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2106,plain,
% 2.69/1.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 2.69/1.04      | v1_relat_1(sK4) = iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1178,c_1196]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2337,plain,
% 2.69/1.04      ( v1_relat_1(sK4) = iProver_top ),
% 2.69/1.04      inference(global_propositional_subsumption,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_2106,c_36,c_1614,c_1938]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_8,plain,
% 2.69/1.04      ( ~ v1_relat_1(X0)
% 2.69/1.04      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.69/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_1189,plain,
% 2.69/1.04      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.69/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_2342,plain,
% 2.69/1.04      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_2337,c_1189]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_3736,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.69/1.04      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 2.69/1.04      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.69/1.04      | v1_relat_1(X2) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_1184,c_1186]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10279,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
% 2.69/1.04      | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
% 2.69/1.04      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top
% 2.69/1.04      | v1_relat_1(k7_relat_1(sK4,X2)) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_2342,c_3736]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10367,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
% 2.69/1.04      | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
% 2.69/1.04      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top ),
% 2.69/1.04      inference(forward_subsumption_resolution,
% 2.69/1.04                [status(thm)],
% 2.69/1.04                [c_10279,c_2489]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10372,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 2.69/1.04      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 2.69/1.04      | r1_tarski(sK1,X0) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_3321,c_10367]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10400,plain,
% 2.69/1.04      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 2.69/1.04      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 2.69/1.04      | r1_tarski(sK1,X0) != iProver_top ),
% 2.69/1.04      inference(light_normalisation,[status(thm)],[c_10372,c_3321]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10508,plain,
% 2.69/1.04      ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
% 2.69/1.04      | r1_tarski(sK1,X0) != iProver_top ),
% 2.69/1.04      inference(superposition,[status(thm)],[c_2320,c_10400]) ).
% 2.69/1.04  
% 2.69/1.04  cnf(c_10516,plain,
% 2.69/1.05      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
% 2.69/1.05      inference(superposition,[status(thm)],[c_3503,c_10508]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_22,plain,
% 2.69/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.05      | ~ v1_funct_1(X0)
% 2.69/1.05      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.69/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1181,plain,
% 2.69/1.05      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 2.69/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.69/1.05      | v1_funct_1(X2) != iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_2887,plain,
% 2.69/1.05      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 2.69/1.05      | v1_funct_1(sK4) != iProver_top ),
% 2.69/1.05      inference(superposition,[status(thm)],[c_1178,c_1181]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_31,negated_conjecture,
% 2.69/1.05      ( v1_funct_1(sK4) ),
% 2.69/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1490,plain,
% 2.69/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.69/1.05      | ~ v1_funct_1(sK4)
% 2.69/1.05      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 2.69/1.05      inference(instantiation,[status(thm)],[c_22]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1590,plain,
% 2.69/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.69/1.05      | ~ v1_funct_1(sK4)
% 2.69/1.05      | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 2.69/1.05      inference(instantiation,[status(thm)],[c_1490]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3132,plain,
% 2.69/1.05      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 2.69/1.05      inference(global_propositional_subsumption,
% 2.69/1.05                [status(thm)],
% 2.69/1.05                [c_2887,c_31,c_29,c_1590]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_24,plain,
% 2.69/1.05      ( v1_funct_2(X0,X1,X2)
% 2.69/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.05      | ~ v1_funct_1(X0)
% 2.69/1.05      | k1_relset_1(X1,X2,X0) != X1 ),
% 2.69/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_26,negated_conjecture,
% 2.69/1.05      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 2.69/1.05      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.69/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 2.69/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_451,plain,
% 2.69/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.05      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.69/1.05      | ~ v1_funct_1(X0)
% 2.69/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.69/1.05      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 2.69/1.05      | k1_relset_1(X1,X2,X0) != X1
% 2.69/1.05      | sK2 != X2
% 2.69/1.05      | sK1 != X1 ),
% 2.69/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_452,plain,
% 2.69/1.05      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.69/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.69/1.05      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.69/1.05      inference(unflattening,[status(thm)],[c_451]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1172,plain,
% 2.69/1.05      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.69/1.05      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.69/1.05      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3139,plain,
% 2.69/1.05      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
% 2.69/1.05      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.69/1.05      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 2.69/1.05      inference(demodulation,[status(thm)],[c_3132,c_1172]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_21,plain,
% 2.69/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.05      | ~ v1_funct_1(X0)
% 2.69/1.05      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 2.69/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1182,plain,
% 2.69/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.05      | v1_funct_1(X0) != iProver_top
% 2.69/1.05      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3091,plain,
% 2.69/1.05      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 2.69/1.05      | v1_funct_1(sK4) != iProver_top ),
% 2.69/1.05      inference(superposition,[status(thm)],[c_1178,c_1182]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_34,plain,
% 2.69/1.05      ( v1_funct_1(sK4) = iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1451,plain,
% 2.69/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.69/1.05      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 2.69/1.05      | ~ v1_funct_1(sK4) ),
% 2.69/1.05      inference(instantiation,[status(thm)],[c_21]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1585,plain,
% 2.69/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.69/1.05      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
% 2.69/1.05      | ~ v1_funct_1(sK4) ),
% 2.69/1.05      inference(instantiation,[status(thm)],[c_1451]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_1586,plain,
% 2.69/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.69/1.05      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 2.69/1.05      | v1_funct_1(sK4) != iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_1585]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3096,plain,
% 2.69/1.05      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
% 2.69/1.05      inference(global_propositional_subsumption,
% 2.69/1.05                [status(thm)],
% 2.69/1.05                [c_3091,c_34,c_36,c_1586]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3140,plain,
% 2.69/1.05      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 2.69/1.05      inference(demodulation,[status(thm)],[c_3132,c_3096]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_3146,plain,
% 2.69/1.05      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
% 2.69/1.05      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.69/1.05      inference(forward_subsumption_resolution,
% 2.69/1.05                [status(thm)],
% 2.69/1.05                [c_3139,c_3140]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_10954,plain,
% 2.69/1.05      ( sK1 != sK1
% 2.69/1.05      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.69/1.05      inference(demodulation,[status(thm)],[c_10516,c_3146]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_11102,plain,
% 2.69/1.05      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.69/1.05      inference(equality_resolution_simp,[status(thm)],[c_10954]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_11105,plain,
% 2.69/1.05      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 2.69/1.05      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 2.69/1.05      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 2.69/1.05      inference(superposition,[status(thm)],[c_1184,c_11102]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_11106,plain,
% 2.69/1.05      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 2.69/1.05      | r1_tarski(sK1,sK1) != iProver_top
% 2.69/1.05      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 2.69/1.05      inference(light_normalisation,[status(thm)],[c_11105,c_3321]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_11107,plain,
% 2.69/1.05      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 2.69/1.05      | r1_tarski(sK1,sK1) != iProver_top
% 2.69/1.05      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 2.69/1.05      inference(demodulation,[status(thm)],[c_11106,c_2342]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_8363,plain,
% 2.69/1.05      ( ~ v4_relat_1(sK4,sK0)
% 2.69/1.05      | v1_relat_1(k7_relat_1(sK4,sK1))
% 2.69/1.05      | ~ v1_relat_1(sK4) ),
% 2.69/1.05      inference(instantiation,[status(thm)],[c_2162]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(c_8364,plain,
% 2.69/1.05      ( v4_relat_1(sK4,sK0) != iProver_top
% 2.69/1.05      | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
% 2.69/1.05      | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.05      inference(predicate_to_equality,[status(thm)],[c_8363]) ).
% 2.69/1.05  
% 2.69/1.05  cnf(contradiction,plain,
% 2.69/1.05      ( $false ),
% 2.69/1.05      inference(minisat,
% 2.69/1.05                [status(thm)],
% 2.69/1.05                [c_11107,c_8364,c_3503,c_2320,c_1938,c_1614,c_1432,c_36]) ).
% 2.69/1.05  
% 2.69/1.05  
% 2.69/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.05  
% 2.69/1.05  ------                               Statistics
% 2.69/1.05  
% 2.69/1.05  ------ General
% 2.69/1.05  
% 2.69/1.05  abstr_ref_over_cycles:                  0
% 2.69/1.05  abstr_ref_under_cycles:                 0
% 2.69/1.05  gc_basic_clause_elim:                   0
% 2.69/1.05  forced_gc_time:                         0
% 2.69/1.05  parsing_time:                           0.016
% 2.69/1.05  unif_index_cands_time:                  0.
% 2.69/1.05  unif_index_add_time:                    0.
% 2.69/1.05  orderings_time:                         0.
% 2.69/1.05  out_proof_time:                         0.013
% 2.69/1.05  total_time:                             0.355
% 2.69/1.05  num_of_symbols:                         53
% 2.69/1.05  num_of_terms:                           11856
% 2.69/1.05  
% 2.69/1.05  ------ Preprocessing
% 2.69/1.05  
% 2.69/1.05  num_of_splits:                          0
% 2.69/1.05  num_of_split_atoms:                     0
% 2.69/1.05  num_of_reused_defs:                     0
% 2.69/1.05  num_eq_ax_congr_red:                    17
% 2.69/1.05  num_of_sem_filtered_clauses:            1
% 2.69/1.05  num_of_subtypes:                        0
% 2.69/1.05  monotx_restored_types:                  0
% 2.69/1.05  sat_num_of_epr_types:                   0
% 2.69/1.05  sat_num_of_non_cyclic_types:            0
% 2.69/1.05  sat_guarded_non_collapsed_types:        0
% 2.69/1.05  num_pure_diseq_elim:                    0
% 2.69/1.05  simp_replaced_by:                       0
% 2.69/1.05  res_preprocessed:                       144
% 2.69/1.05  prep_upred:                             0
% 2.69/1.05  prep_unflattend:                        42
% 2.69/1.05  smt_new_axioms:                         0
% 2.69/1.05  pred_elim_cands:                        5
% 2.69/1.05  pred_elim:                              2
% 2.69/1.05  pred_elim_cl:                           3
% 2.69/1.05  pred_elim_cycles:                       4
% 2.69/1.05  merged_defs:                            0
% 2.69/1.05  merged_defs_ncl:                        0
% 2.69/1.05  bin_hyper_res:                          0
% 2.69/1.05  prep_cycles:                            4
% 2.69/1.05  pred_elim_time:                         0.005
% 2.69/1.05  splitting_time:                         0.
% 2.69/1.05  sem_filter_time:                        0.
% 2.69/1.05  monotx_time:                            0.
% 2.69/1.05  subtype_inf_time:                       0.
% 2.69/1.05  
% 2.69/1.05  ------ Problem properties
% 2.69/1.05  
% 2.69/1.05  clauses:                                28
% 2.69/1.05  conjectures:                            4
% 2.69/1.05  epr:                                    3
% 2.69/1.05  horn:                                   26
% 2.69/1.05  ground:                                 11
% 2.69/1.05  unary:                                  6
% 2.69/1.05  binary:                                 5
% 2.69/1.05  lits:                                   77
% 2.69/1.05  lits_eq:                                22
% 2.69/1.05  fd_pure:                                0
% 2.69/1.05  fd_pseudo:                              0
% 2.69/1.05  fd_cond:                                1
% 2.69/1.05  fd_pseudo_cond:                         0
% 2.69/1.05  ac_symbols:                             0
% 2.69/1.05  
% 2.69/1.05  ------ Propositional Solver
% 2.69/1.05  
% 2.69/1.05  prop_solver_calls:                      30
% 2.69/1.05  prop_fast_solver_calls:                 1240
% 2.69/1.05  smt_solver_calls:                       0
% 2.69/1.05  smt_fast_solver_calls:                  0
% 2.69/1.05  prop_num_of_clauses:                    4011
% 2.69/1.05  prop_preprocess_simplified:             8599
% 2.69/1.05  prop_fo_subsumed:                       32
% 2.69/1.05  prop_solver_time:                       0.
% 2.69/1.05  smt_solver_time:                        0.
% 2.69/1.05  smt_fast_solver_time:                   0.
% 2.69/1.05  prop_fast_solver_time:                  0.
% 2.69/1.05  prop_unsat_core_time:                   0.
% 2.69/1.05  
% 2.69/1.05  ------ QBF
% 2.69/1.05  
% 2.69/1.05  qbf_q_res:                              0
% 2.69/1.05  qbf_num_tautologies:                    0
% 2.69/1.05  qbf_prep_cycles:                        0
% 2.69/1.05  
% 2.69/1.05  ------ BMC1
% 2.69/1.05  
% 2.69/1.05  bmc1_current_bound:                     -1
% 2.69/1.05  bmc1_last_solved_bound:                 -1
% 2.69/1.05  bmc1_unsat_core_size:                   -1
% 2.69/1.05  bmc1_unsat_core_parents_size:           -1
% 2.69/1.05  bmc1_merge_next_fun:                    0
% 2.69/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.05  
% 2.69/1.05  ------ Instantiation
% 2.69/1.05  
% 2.69/1.05  inst_num_of_clauses:                    1041
% 2.69/1.05  inst_num_in_passive:                    59
% 2.69/1.05  inst_num_in_active:                     654
% 2.69/1.05  inst_num_in_unprocessed:                328
% 2.69/1.05  inst_num_of_loops:                      670
% 2.69/1.05  inst_num_of_learning_restarts:          0
% 2.69/1.05  inst_num_moves_active_passive:          8
% 2.69/1.05  inst_lit_activity:                      0
% 2.69/1.05  inst_lit_activity_moves:                0
% 2.69/1.05  inst_num_tautologies:                   0
% 2.69/1.05  inst_num_prop_implied:                  0
% 2.69/1.05  inst_num_existing_simplified:           0
% 2.69/1.05  inst_num_eq_res_simplified:             0
% 2.69/1.05  inst_num_child_elim:                    0
% 2.69/1.05  inst_num_of_dismatching_blockings:      141
% 2.69/1.05  inst_num_of_non_proper_insts:           912
% 2.69/1.05  inst_num_of_duplicates:                 0
% 2.69/1.05  inst_inst_num_from_inst_to_res:         0
% 2.69/1.05  inst_dismatching_checking_time:         0.
% 2.69/1.05  
% 2.69/1.05  ------ Resolution
% 2.69/1.05  
% 2.69/1.05  res_num_of_clauses:                     0
% 2.69/1.05  res_num_in_passive:                     0
% 2.69/1.05  res_num_in_active:                      0
% 2.69/1.05  res_num_of_loops:                       148
% 2.69/1.05  res_forward_subset_subsumed:            68
% 2.69/1.05  res_backward_subset_subsumed:           8
% 2.69/1.05  res_forward_subsumed:                   0
% 2.69/1.05  res_backward_subsumed:                  0
% 2.69/1.05  res_forward_subsumption_resolution:     0
% 2.69/1.05  res_backward_subsumption_resolution:    0
% 2.69/1.05  res_clause_to_clause_subsumption:       542
% 2.69/1.05  res_orphan_elimination:                 0
% 2.69/1.05  res_tautology_del:                      153
% 2.69/1.05  res_num_eq_res_simplified:              0
% 2.69/1.05  res_num_sel_changes:                    0
% 2.69/1.05  res_moves_from_active_to_pass:          0
% 2.69/1.05  
% 2.69/1.05  ------ Superposition
% 2.69/1.05  
% 2.69/1.05  sup_time_total:                         0.
% 2.69/1.05  sup_time_generating:                    0.
% 2.69/1.05  sup_time_sim_full:                      0.
% 2.69/1.05  sup_time_sim_immed:                     0.
% 2.69/1.05  
% 2.69/1.05  sup_num_of_clauses:                     255
% 2.69/1.05  sup_num_in_active:                      123
% 2.69/1.05  sup_num_in_passive:                     132
% 2.69/1.05  sup_num_of_loops:                       132
% 2.69/1.05  sup_fw_superposition:                   223
% 2.69/1.05  sup_bw_superposition:                   145
% 2.69/1.05  sup_immediate_simplified:               127
% 2.69/1.05  sup_given_eliminated:                   0
% 2.69/1.05  comparisons_done:                       0
% 2.69/1.05  comparisons_avoided:                    0
% 2.69/1.05  
% 2.69/1.05  ------ Simplifications
% 2.69/1.05  
% 2.69/1.05  
% 2.69/1.05  sim_fw_subset_subsumed:                 15
% 2.69/1.05  sim_bw_subset_subsumed:                 3
% 2.69/1.05  sim_fw_subsumed:                        47
% 2.69/1.05  sim_bw_subsumed:                        0
% 2.69/1.05  sim_fw_subsumption_res:                 26
% 2.69/1.05  sim_bw_subsumption_res:                 0
% 2.69/1.05  sim_tautology_del:                      8
% 2.69/1.05  sim_eq_tautology_del:                   45
% 2.69/1.05  sim_eq_res_simp:                        1
% 2.69/1.05  sim_fw_demodulated:                     3
% 2.69/1.05  sim_bw_demodulated:                     9
% 2.69/1.05  sim_light_normalised:                   86
% 2.69/1.05  sim_joinable_taut:                      0
% 2.69/1.05  sim_joinable_simp:                      0
% 2.69/1.05  sim_ac_normalised:                      0
% 2.69/1.05  sim_smt_subsumption:                    0
% 2.69/1.05  
%------------------------------------------------------------------------------
