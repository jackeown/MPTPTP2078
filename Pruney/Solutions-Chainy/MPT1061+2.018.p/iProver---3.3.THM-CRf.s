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
% DateTime   : Thu Dec  3 12:09:32 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  200 (4454 expanded)
%              Number of clauses        :  128 (1696 expanded)
%              Number of leaves         :   19 ( 964 expanded)
%              Depth                    :   32
%              Number of atoms          :  596 (23461 expanded)
%              Number of equality atoms :  284 (3087 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f48,f47])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f80,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1703,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1707,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3319,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_1707])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3441,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3319,c_38])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3233,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_1708])).

cnf(c_3330,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_38])).

cnf(c_3449,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_3330])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1717,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1718,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2348,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_1718])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_279,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_341,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_279])).

cnf(c_1701,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_4534,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_1701])).

cnf(c_4722,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_4534])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1704,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_627,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_629,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1712,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2603,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1703,c_1712])).

cnf(c_2711,plain,
    ( k1_relat_1(sK4) = sK0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_629,c_2603])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_463,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_36])).

cnf(c_2918,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_463])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1713,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3106,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_1713])).

cnf(c_3650,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1704,c_3106])).

cnf(c_4805,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_4722,c_3650])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4900,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k7_relat_1(sK4,sK1))))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_1706])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1716,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4803,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_4722,c_1716])).

cnf(c_4904,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4900,c_4803])).

cnf(c_7542,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4904,c_1718])).

cnf(c_6983,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK1),X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(sK4,sK1)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_8292,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK1),sK4)
    | v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6983])).

cnf(c_8293,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8292])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7711,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_17339,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7711])).

cnf(c_17340,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17339])).

cnf(c_20949,plain,
    ( v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7542,c_4722,c_8293,c_17340])).

cnf(c_20950,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20949])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1722,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_20954,plain,
    ( k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)) = k7_relat_1(sK4,sK1)
    | r1_tarski(k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)),k7_relat_1(sK4,sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20950,c_1722])).

cnf(c_1719,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1721,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1711,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2706,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1703,c_1711])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1705,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2811,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2706,c_1705])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3978,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_1712])).

cnf(c_23196,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_3978])).

cnf(c_23254,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23196,c_4805])).

cnf(c_23255,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23254,c_4803])).

cnf(c_24488,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23255,c_4722,c_8293,c_17340])).

cnf(c_24489,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24488])).

cnf(c_24497,plain,
    ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_24489])).

cnf(c_24511,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1721,c_24497])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_611,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_1694,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_612,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1780,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1781,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_1988,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1694,c_38,c_40,c_612,c_1781])).

cnf(c_1989,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1988])).

cnf(c_3448,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_1989])).

cnf(c_24593,plain,
    ( sK2 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24511,c_3448])).

cnf(c_24818,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_24593])).

cnf(c_24820,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_24818])).

cnf(c_3211,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3212,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3211])).

cnf(c_24821,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_24818])).

cnf(c_24822,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24821,c_4805])).

cnf(c_24823,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24822,c_4803])).

cnf(c_24827,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24820,c_2811,c_3212,c_4722,c_8293,c_17340,c_24823])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_637,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_638,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2 ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_1693,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_639,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_2295,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1693,c_38,c_40,c_639,c_1781])).

cnf(c_2296,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2295])).

cnf(c_3445,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
    | k2_relat_1(k7_relat_1(sK4,sK1)) != sK2
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_2296])).

cnf(c_4895,plain,
    ( k2_relat_1(k7_relat_1(sK4,sK1)) != sK2
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4805,c_3445])).

cnf(c_4896,plain,
    ( k9_relat_1(sK4,sK1) != sK2
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4895,c_4803])).

cnf(c_4897,plain,
    ( k9_relat_1(sK4,sK1) != sK2
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4896])).

cnf(c_22036,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k9_relat_1(sK4,sK1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4897,c_4722,c_8293,c_17340])).

cnf(c_22037,plain,
    ( k9_relat_1(sK4,sK1) != sK2
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22036])).

cnf(c_24842,plain,
    ( k9_relat_1(sK4,sK1) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24827,c_22037])).

cnf(c_24915,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24827,c_2811])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1720,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2609,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_1722])).

cnf(c_25417,plain,
    ( k9_relat_1(sK4,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24915,c_2609])).

cnf(c_25891,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25417,c_4904])).

cnf(c_26389,plain,
    ( v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20954,c_4722,c_8293,c_17340,c_24842,c_25417,c_25891])).

cnf(c_26393,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3449,c_26389])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.67/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.49  
% 7.67/1.49  ------  iProver source info
% 7.67/1.49  
% 7.67/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.49  git: non_committed_changes: false
% 7.67/1.49  git: last_make_outside_of_git: false
% 7.67/1.49  
% 7.67/1.49  ------ 
% 7.67/1.49  
% 7.67/1.49  ------ Input Options
% 7.67/1.49  
% 7.67/1.49  --out_options                           all
% 7.67/1.49  --tptp_safe_out                         true
% 7.67/1.49  --problem_path                          ""
% 7.67/1.49  --include_path                          ""
% 7.67/1.49  --clausifier                            res/vclausify_rel
% 7.67/1.49  --clausifier_options                    ""
% 7.67/1.49  --stdin                                 false
% 7.67/1.49  --stats_out                             all
% 7.67/1.49  
% 7.67/1.49  ------ General Options
% 7.67/1.49  
% 7.67/1.49  --fof                                   false
% 7.67/1.49  --time_out_real                         305.
% 7.67/1.49  --time_out_virtual                      -1.
% 7.67/1.49  --symbol_type_check                     false
% 7.67/1.49  --clausify_out                          false
% 7.67/1.49  --sig_cnt_out                           false
% 7.67/1.49  --trig_cnt_out                          false
% 7.67/1.49  --trig_cnt_out_tolerance                1.
% 7.67/1.49  --trig_cnt_out_sk_spl                   false
% 7.67/1.49  --abstr_cl_out                          false
% 7.67/1.49  
% 7.67/1.49  ------ Global Options
% 7.67/1.49  
% 7.67/1.49  --schedule                              default
% 7.67/1.49  --add_important_lit                     false
% 7.67/1.49  --prop_solver_per_cl                    1000
% 7.67/1.49  --min_unsat_core                        false
% 7.67/1.49  --soft_assumptions                      false
% 7.67/1.49  --soft_lemma_size                       3
% 7.67/1.49  --prop_impl_unit_size                   0
% 7.67/1.49  --prop_impl_unit                        []
% 7.67/1.49  --share_sel_clauses                     true
% 7.67/1.49  --reset_solvers                         false
% 7.67/1.49  --bc_imp_inh                            [conj_cone]
% 7.67/1.49  --conj_cone_tolerance                   3.
% 7.67/1.49  --extra_neg_conj                        none
% 7.67/1.49  --large_theory_mode                     true
% 7.67/1.49  --prolific_symb_bound                   200
% 7.67/1.49  --lt_threshold                          2000
% 7.67/1.49  --clause_weak_htbl                      true
% 7.67/1.49  --gc_record_bc_elim                     false
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing Options
% 7.67/1.49  
% 7.67/1.49  --preprocessing_flag                    true
% 7.67/1.49  --time_out_prep_mult                    0.1
% 7.67/1.49  --splitting_mode                        input
% 7.67/1.49  --splitting_grd                         true
% 7.67/1.49  --splitting_cvd                         false
% 7.67/1.49  --splitting_cvd_svl                     false
% 7.67/1.49  --splitting_nvd                         32
% 7.67/1.49  --sub_typing                            true
% 7.67/1.49  --prep_gs_sim                           true
% 7.67/1.49  --prep_unflatten                        true
% 7.67/1.49  --prep_res_sim                          true
% 7.67/1.49  --prep_upred                            true
% 7.67/1.49  --prep_sem_filter                       exhaustive
% 7.67/1.49  --prep_sem_filter_out                   false
% 7.67/1.49  --pred_elim                             true
% 7.67/1.49  --res_sim_input                         true
% 7.67/1.49  --eq_ax_congr_red                       true
% 7.67/1.49  --pure_diseq_elim                       true
% 7.67/1.49  --brand_transform                       false
% 7.67/1.49  --non_eq_to_eq                          false
% 7.67/1.49  --prep_def_merge                        true
% 7.67/1.49  --prep_def_merge_prop_impl              false
% 7.67/1.49  --prep_def_merge_mbd                    true
% 7.67/1.49  --prep_def_merge_tr_red                 false
% 7.67/1.49  --prep_def_merge_tr_cl                  false
% 7.67/1.49  --smt_preprocessing                     true
% 7.67/1.49  --smt_ac_axioms                         fast
% 7.67/1.49  --preprocessed_out                      false
% 7.67/1.49  --preprocessed_stats                    false
% 7.67/1.49  
% 7.67/1.49  ------ Abstraction refinement Options
% 7.67/1.49  
% 7.67/1.49  --abstr_ref                             []
% 7.67/1.49  --abstr_ref_prep                        false
% 7.67/1.49  --abstr_ref_until_sat                   false
% 7.67/1.49  --abstr_ref_sig_restrict                funpre
% 7.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.49  --abstr_ref_under                       []
% 7.67/1.49  
% 7.67/1.49  ------ SAT Options
% 7.67/1.49  
% 7.67/1.49  --sat_mode                              false
% 7.67/1.49  --sat_fm_restart_options                ""
% 7.67/1.49  --sat_gr_def                            false
% 7.67/1.49  --sat_epr_types                         true
% 7.67/1.49  --sat_non_cyclic_types                  false
% 7.67/1.49  --sat_finite_models                     false
% 7.67/1.49  --sat_fm_lemmas                         false
% 7.67/1.49  --sat_fm_prep                           false
% 7.67/1.49  --sat_fm_uc_incr                        true
% 7.67/1.49  --sat_out_model                         small
% 7.67/1.49  --sat_out_clauses                       false
% 7.67/1.49  
% 7.67/1.49  ------ QBF Options
% 7.67/1.49  
% 7.67/1.49  --qbf_mode                              false
% 7.67/1.49  --qbf_elim_univ                         false
% 7.67/1.49  --qbf_dom_inst                          none
% 7.67/1.49  --qbf_dom_pre_inst                      false
% 7.67/1.49  --qbf_sk_in                             false
% 7.67/1.49  --qbf_pred_elim                         true
% 7.67/1.49  --qbf_split                             512
% 7.67/1.49  
% 7.67/1.49  ------ BMC1 Options
% 7.67/1.49  
% 7.67/1.49  --bmc1_incremental                      false
% 7.67/1.49  --bmc1_axioms                           reachable_all
% 7.67/1.49  --bmc1_min_bound                        0
% 7.67/1.49  --bmc1_max_bound                        -1
% 7.67/1.49  --bmc1_max_bound_default                -1
% 7.67/1.49  --bmc1_symbol_reachability              true
% 7.67/1.49  --bmc1_property_lemmas                  false
% 7.67/1.49  --bmc1_k_induction                      false
% 7.67/1.49  --bmc1_non_equiv_states                 false
% 7.67/1.49  --bmc1_deadlock                         false
% 7.67/1.49  --bmc1_ucm                              false
% 7.67/1.49  --bmc1_add_unsat_core                   none
% 7.67/1.49  --bmc1_unsat_core_children              false
% 7.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.49  --bmc1_out_stat                         full
% 7.67/1.49  --bmc1_ground_init                      false
% 7.67/1.49  --bmc1_pre_inst_next_state              false
% 7.67/1.49  --bmc1_pre_inst_state                   false
% 7.67/1.49  --bmc1_pre_inst_reach_state             false
% 7.67/1.49  --bmc1_out_unsat_core                   false
% 7.67/1.49  --bmc1_aig_witness_out                  false
% 7.67/1.49  --bmc1_verbose                          false
% 7.67/1.49  --bmc1_dump_clauses_tptp                false
% 7.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.49  --bmc1_dump_file                        -
% 7.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.49  --bmc1_ucm_extend_mode                  1
% 7.67/1.49  --bmc1_ucm_init_mode                    2
% 7.67/1.49  --bmc1_ucm_cone_mode                    none
% 7.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.49  --bmc1_ucm_relax_model                  4
% 7.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.49  --bmc1_ucm_layered_model                none
% 7.67/1.49  --bmc1_ucm_max_lemma_size               10
% 7.67/1.49  
% 7.67/1.49  ------ AIG Options
% 7.67/1.49  
% 7.67/1.49  --aig_mode                              false
% 7.67/1.49  
% 7.67/1.49  ------ Instantiation Options
% 7.67/1.49  
% 7.67/1.49  --instantiation_flag                    true
% 7.67/1.49  --inst_sos_flag                         true
% 7.67/1.49  --inst_sos_phase                        true
% 7.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.49  --inst_lit_sel_side                     num_symb
% 7.67/1.49  --inst_solver_per_active                1400
% 7.67/1.49  --inst_solver_calls_frac                1.
% 7.67/1.49  --inst_passive_queue_type               priority_queues
% 7.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.49  --inst_passive_queues_freq              [25;2]
% 7.67/1.49  --inst_dismatching                      true
% 7.67/1.49  --inst_eager_unprocessed_to_passive     true
% 7.67/1.49  --inst_prop_sim_given                   true
% 7.67/1.49  --inst_prop_sim_new                     false
% 7.67/1.49  --inst_subs_new                         false
% 7.67/1.49  --inst_eq_res_simp                      false
% 7.67/1.49  --inst_subs_given                       false
% 7.67/1.49  --inst_orphan_elimination               true
% 7.67/1.49  --inst_learning_loop_flag               true
% 7.67/1.49  --inst_learning_start                   3000
% 7.67/1.49  --inst_learning_factor                  2
% 7.67/1.49  --inst_start_prop_sim_after_learn       3
% 7.67/1.49  --inst_sel_renew                        solver
% 7.67/1.49  --inst_lit_activity_flag                true
% 7.67/1.49  --inst_restr_to_given                   false
% 7.67/1.49  --inst_activity_threshold               500
% 7.67/1.49  --inst_out_proof                        true
% 7.67/1.49  
% 7.67/1.49  ------ Resolution Options
% 7.67/1.49  
% 7.67/1.49  --resolution_flag                       true
% 7.67/1.49  --res_lit_sel                           adaptive
% 7.67/1.49  --res_lit_sel_side                      none
% 7.67/1.49  --res_ordering                          kbo
% 7.67/1.49  --res_to_prop_solver                    active
% 7.67/1.49  --res_prop_simpl_new                    false
% 7.67/1.49  --res_prop_simpl_given                  true
% 7.67/1.49  --res_passive_queue_type                priority_queues
% 7.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.49  --res_passive_queues_freq               [15;5]
% 7.67/1.49  --res_forward_subs                      full
% 7.67/1.49  --res_backward_subs                     full
% 7.67/1.49  --res_forward_subs_resolution           true
% 7.67/1.49  --res_backward_subs_resolution          true
% 7.67/1.49  --res_orphan_elimination                true
% 7.67/1.49  --res_time_limit                        2.
% 7.67/1.49  --res_out_proof                         true
% 7.67/1.49  
% 7.67/1.49  ------ Superposition Options
% 7.67/1.49  
% 7.67/1.49  --superposition_flag                    true
% 7.67/1.49  --sup_passive_queue_type                priority_queues
% 7.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.49  --demod_completeness_check              fast
% 7.67/1.49  --demod_use_ground                      true
% 7.67/1.49  --sup_to_prop_solver                    passive
% 7.67/1.49  --sup_prop_simpl_new                    true
% 7.67/1.49  --sup_prop_simpl_given                  true
% 7.67/1.49  --sup_fun_splitting                     true
% 7.67/1.49  --sup_smt_interval                      50000
% 7.67/1.49  
% 7.67/1.49  ------ Superposition Simplification Setup
% 7.67/1.49  
% 7.67/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.49  --sup_immed_triv                        [TrivRules]
% 7.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_immed_bw_main                     []
% 7.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_input_bw                          []
% 7.67/1.49  
% 7.67/1.49  ------ Combination Options
% 7.67/1.49  
% 7.67/1.49  --comb_res_mult                         3
% 7.67/1.49  --comb_sup_mult                         2
% 7.67/1.49  --comb_inst_mult                        10
% 7.67/1.49  
% 7.67/1.49  ------ Debug Options
% 7.67/1.49  
% 7.67/1.49  --dbg_backtrace                         false
% 7.67/1.49  --dbg_dump_prop_clauses                 false
% 7.67/1.49  --dbg_dump_prop_clauses_file            -
% 7.67/1.49  --dbg_out_stat                          false
% 7.67/1.49  ------ Parsing...
% 7.67/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  ------ Proving...
% 7.67/1.49  ------ Problem Properties 
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  clauses                                 33
% 7.67/1.49  conjectures                             4
% 7.67/1.49  EPR                                     7
% 7.67/1.49  Horn                                    30
% 7.67/1.49  unary                                   8
% 7.67/1.49  binary                                  8
% 7.67/1.49  lits                                    92
% 7.67/1.49  lits eq                                 30
% 7.67/1.49  fd_pure                                 0
% 7.67/1.49  fd_pseudo                               0
% 7.67/1.49  fd_cond                                 1
% 7.67/1.49  fd_pseudo_cond                          1
% 7.67/1.49  AC symbols                              0
% 7.67/1.49  
% 7.67/1.49  ------ Schedule dynamic 5 is on 
% 7.67/1.49  
% 7.67/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ 
% 7.67/1.49  Current options:
% 7.67/1.49  ------ 
% 7.67/1.49  
% 7.67/1.49  ------ Input Options
% 7.67/1.49  
% 7.67/1.49  --out_options                           all
% 7.67/1.49  --tptp_safe_out                         true
% 7.67/1.49  --problem_path                          ""
% 7.67/1.49  --include_path                          ""
% 7.67/1.49  --clausifier                            res/vclausify_rel
% 7.67/1.49  --clausifier_options                    ""
% 7.67/1.49  --stdin                                 false
% 7.67/1.49  --stats_out                             all
% 7.67/1.49  
% 7.67/1.49  ------ General Options
% 7.67/1.49  
% 7.67/1.49  --fof                                   false
% 7.67/1.49  --time_out_real                         305.
% 7.67/1.49  --time_out_virtual                      -1.
% 7.67/1.49  --symbol_type_check                     false
% 7.67/1.49  --clausify_out                          false
% 7.67/1.49  --sig_cnt_out                           false
% 7.67/1.49  --trig_cnt_out                          false
% 7.67/1.49  --trig_cnt_out_tolerance                1.
% 7.67/1.49  --trig_cnt_out_sk_spl                   false
% 7.67/1.49  --abstr_cl_out                          false
% 7.67/1.49  
% 7.67/1.49  ------ Global Options
% 7.67/1.49  
% 7.67/1.49  --schedule                              default
% 7.67/1.49  --add_important_lit                     false
% 7.67/1.49  --prop_solver_per_cl                    1000
% 7.67/1.49  --min_unsat_core                        false
% 7.67/1.49  --soft_assumptions                      false
% 7.67/1.49  --soft_lemma_size                       3
% 7.67/1.49  --prop_impl_unit_size                   0
% 7.67/1.49  --prop_impl_unit                        []
% 7.67/1.49  --share_sel_clauses                     true
% 7.67/1.49  --reset_solvers                         false
% 7.67/1.49  --bc_imp_inh                            [conj_cone]
% 7.67/1.49  --conj_cone_tolerance                   3.
% 7.67/1.49  --extra_neg_conj                        none
% 7.67/1.49  --large_theory_mode                     true
% 7.67/1.49  --prolific_symb_bound                   200
% 7.67/1.49  --lt_threshold                          2000
% 7.67/1.49  --clause_weak_htbl                      true
% 7.67/1.49  --gc_record_bc_elim                     false
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing Options
% 7.67/1.49  
% 7.67/1.49  --preprocessing_flag                    true
% 7.67/1.49  --time_out_prep_mult                    0.1
% 7.67/1.49  --splitting_mode                        input
% 7.67/1.49  --splitting_grd                         true
% 7.67/1.49  --splitting_cvd                         false
% 7.67/1.49  --splitting_cvd_svl                     false
% 7.67/1.49  --splitting_nvd                         32
% 7.67/1.49  --sub_typing                            true
% 7.67/1.49  --prep_gs_sim                           true
% 7.67/1.49  --prep_unflatten                        true
% 7.67/1.49  --prep_res_sim                          true
% 7.67/1.49  --prep_upred                            true
% 7.67/1.49  --prep_sem_filter                       exhaustive
% 7.67/1.49  --prep_sem_filter_out                   false
% 7.67/1.49  --pred_elim                             true
% 7.67/1.49  --res_sim_input                         true
% 7.67/1.49  --eq_ax_congr_red                       true
% 7.67/1.49  --pure_diseq_elim                       true
% 7.67/1.49  --brand_transform                       false
% 7.67/1.49  --non_eq_to_eq                          false
% 7.67/1.49  --prep_def_merge                        true
% 7.67/1.49  --prep_def_merge_prop_impl              false
% 7.67/1.49  --prep_def_merge_mbd                    true
% 7.67/1.49  --prep_def_merge_tr_red                 false
% 7.67/1.49  --prep_def_merge_tr_cl                  false
% 7.67/1.49  --smt_preprocessing                     true
% 7.67/1.49  --smt_ac_axioms                         fast
% 7.67/1.49  --preprocessed_out                      false
% 7.67/1.49  --preprocessed_stats                    false
% 7.67/1.49  
% 7.67/1.49  ------ Abstraction refinement Options
% 7.67/1.49  
% 7.67/1.49  --abstr_ref                             []
% 7.67/1.49  --abstr_ref_prep                        false
% 7.67/1.49  --abstr_ref_until_sat                   false
% 7.67/1.49  --abstr_ref_sig_restrict                funpre
% 7.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.49  --abstr_ref_under                       []
% 7.67/1.49  
% 7.67/1.49  ------ SAT Options
% 7.67/1.49  
% 7.67/1.49  --sat_mode                              false
% 7.67/1.49  --sat_fm_restart_options                ""
% 7.67/1.49  --sat_gr_def                            false
% 7.67/1.49  --sat_epr_types                         true
% 7.67/1.49  --sat_non_cyclic_types                  false
% 7.67/1.49  --sat_finite_models                     false
% 7.67/1.49  --sat_fm_lemmas                         false
% 7.67/1.49  --sat_fm_prep                           false
% 7.67/1.49  --sat_fm_uc_incr                        true
% 7.67/1.49  --sat_out_model                         small
% 7.67/1.49  --sat_out_clauses                       false
% 7.67/1.49  
% 7.67/1.49  ------ QBF Options
% 7.67/1.49  
% 7.67/1.49  --qbf_mode                              false
% 7.67/1.49  --qbf_elim_univ                         false
% 7.67/1.49  --qbf_dom_inst                          none
% 7.67/1.49  --qbf_dom_pre_inst                      false
% 7.67/1.49  --qbf_sk_in                             false
% 7.67/1.49  --qbf_pred_elim                         true
% 7.67/1.49  --qbf_split                             512
% 7.67/1.49  
% 7.67/1.49  ------ BMC1 Options
% 7.67/1.49  
% 7.67/1.49  --bmc1_incremental                      false
% 7.67/1.49  --bmc1_axioms                           reachable_all
% 7.67/1.49  --bmc1_min_bound                        0
% 7.67/1.49  --bmc1_max_bound                        -1
% 7.67/1.49  --bmc1_max_bound_default                -1
% 7.67/1.49  --bmc1_symbol_reachability              true
% 7.67/1.49  --bmc1_property_lemmas                  false
% 7.67/1.49  --bmc1_k_induction                      false
% 7.67/1.49  --bmc1_non_equiv_states                 false
% 7.67/1.49  --bmc1_deadlock                         false
% 7.67/1.49  --bmc1_ucm                              false
% 7.67/1.49  --bmc1_add_unsat_core                   none
% 7.67/1.49  --bmc1_unsat_core_children              false
% 7.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.49  --bmc1_out_stat                         full
% 7.67/1.49  --bmc1_ground_init                      false
% 7.67/1.49  --bmc1_pre_inst_next_state              false
% 7.67/1.49  --bmc1_pre_inst_state                   false
% 7.67/1.49  --bmc1_pre_inst_reach_state             false
% 7.67/1.49  --bmc1_out_unsat_core                   false
% 7.67/1.49  --bmc1_aig_witness_out                  false
% 7.67/1.49  --bmc1_verbose                          false
% 7.67/1.49  --bmc1_dump_clauses_tptp                false
% 7.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.49  --bmc1_dump_file                        -
% 7.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.49  --bmc1_ucm_extend_mode                  1
% 7.67/1.49  --bmc1_ucm_init_mode                    2
% 7.67/1.49  --bmc1_ucm_cone_mode                    none
% 7.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.49  --bmc1_ucm_relax_model                  4
% 7.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.49  --bmc1_ucm_layered_model                none
% 7.67/1.49  --bmc1_ucm_max_lemma_size               10
% 7.67/1.49  
% 7.67/1.49  ------ AIG Options
% 7.67/1.49  
% 7.67/1.49  --aig_mode                              false
% 7.67/1.49  
% 7.67/1.49  ------ Instantiation Options
% 7.67/1.49  
% 7.67/1.49  --instantiation_flag                    true
% 7.67/1.49  --inst_sos_flag                         true
% 7.67/1.49  --inst_sos_phase                        true
% 7.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.49  --inst_lit_sel_side                     none
% 7.67/1.49  --inst_solver_per_active                1400
% 7.67/1.49  --inst_solver_calls_frac                1.
% 7.67/1.49  --inst_passive_queue_type               priority_queues
% 7.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.49  --inst_passive_queues_freq              [25;2]
% 7.67/1.49  --inst_dismatching                      true
% 7.67/1.49  --inst_eager_unprocessed_to_passive     true
% 7.67/1.49  --inst_prop_sim_given                   true
% 7.67/1.49  --inst_prop_sim_new                     false
% 7.67/1.49  --inst_subs_new                         false
% 7.67/1.49  --inst_eq_res_simp                      false
% 7.67/1.49  --inst_subs_given                       false
% 7.67/1.49  --inst_orphan_elimination               true
% 7.67/1.49  --inst_learning_loop_flag               true
% 7.67/1.49  --inst_learning_start                   3000
% 7.67/1.49  --inst_learning_factor                  2
% 7.67/1.49  --inst_start_prop_sim_after_learn       3
% 7.67/1.49  --inst_sel_renew                        solver
% 7.67/1.49  --inst_lit_activity_flag                true
% 7.67/1.49  --inst_restr_to_given                   false
% 7.67/1.49  --inst_activity_threshold               500
% 7.67/1.49  --inst_out_proof                        true
% 7.67/1.49  
% 7.67/1.49  ------ Resolution Options
% 7.67/1.49  
% 7.67/1.49  --resolution_flag                       false
% 7.67/1.49  --res_lit_sel                           adaptive
% 7.67/1.49  --res_lit_sel_side                      none
% 7.67/1.49  --res_ordering                          kbo
% 7.67/1.49  --res_to_prop_solver                    active
% 7.67/1.49  --res_prop_simpl_new                    false
% 7.67/1.49  --res_prop_simpl_given                  true
% 7.67/1.49  --res_passive_queue_type                priority_queues
% 7.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.49  --res_passive_queues_freq               [15;5]
% 7.67/1.49  --res_forward_subs                      full
% 7.67/1.49  --res_backward_subs                     full
% 7.67/1.49  --res_forward_subs_resolution           true
% 7.67/1.49  --res_backward_subs_resolution          true
% 7.67/1.49  --res_orphan_elimination                true
% 7.67/1.49  --res_time_limit                        2.
% 7.67/1.49  --res_out_proof                         true
% 7.67/1.49  
% 7.67/1.49  ------ Superposition Options
% 7.67/1.49  
% 7.67/1.49  --superposition_flag                    true
% 7.67/1.49  --sup_passive_queue_type                priority_queues
% 7.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.49  --demod_completeness_check              fast
% 7.67/1.49  --demod_use_ground                      true
% 7.67/1.49  --sup_to_prop_solver                    passive
% 7.67/1.49  --sup_prop_simpl_new                    true
% 7.67/1.49  --sup_prop_simpl_given                  true
% 7.67/1.49  --sup_fun_splitting                     true
% 7.67/1.49  --sup_smt_interval                      50000
% 7.67/1.49  
% 7.67/1.49  ------ Superposition Simplification Setup
% 7.67/1.49  
% 7.67/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.49  --sup_immed_triv                        [TrivRules]
% 7.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_immed_bw_main                     []
% 7.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.49  --sup_input_bw                          []
% 7.67/1.49  
% 7.67/1.49  ------ Combination Options
% 7.67/1.49  
% 7.67/1.49  --comb_res_mult                         3
% 7.67/1.49  --comb_sup_mult                         2
% 7.67/1.49  --comb_inst_mult                        10
% 7.67/1.49  
% 7.67/1.49  ------ Debug Options
% 7.67/1.49  
% 7.67/1.49  --dbg_backtrace                         false
% 7.67/1.49  --dbg_dump_prop_clauses                 false
% 7.67/1.49  --dbg_dump_prop_clauses_file            -
% 7.67/1.49  --dbg_out_stat                          false
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS status Theorem for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49   Resolution empty clause
% 7.67/1.49  
% 7.67/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  fof(f19,conjecture,(
% 7.67/1.49    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f20,negated_conjecture,(
% 7.67/1.49    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 7.67/1.49    inference(negated_conjecture,[],[f19])).
% 7.67/1.49  
% 7.67/1.49  fof(f40,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 7.67/1.49    inference(ennf_transformation,[],[f20])).
% 7.67/1.49  
% 7.67/1.49  fof(f41,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 7.67/1.49    inference(flattening,[],[f40])).
% 7.67/1.49  
% 7.67/1.49  fof(f48,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f47,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f49,plain,(
% 7.67/1.49    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f48,f47])).
% 7.67/1.49  
% 7.67/1.49  fof(f83,plain,(
% 7.67/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f17,axiom,(
% 7.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f36,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.67/1.49    inference(ennf_transformation,[],[f17])).
% 7.67/1.49  
% 7.67/1.49  fof(f37,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.67/1.49    inference(flattening,[],[f36])).
% 7.67/1.49  
% 7.67/1.49  fof(f76,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f37])).
% 7.67/1.49  
% 7.67/1.49  fof(f81,plain,(
% 7.67/1.49    v1_funct_1(sK4)),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f16,axiom,(
% 7.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f34,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.67/1.49    inference(ennf_transformation,[],[f16])).
% 7.67/1.49  
% 7.67/1.49  fof(f35,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.67/1.49    inference(flattening,[],[f34])).
% 7.67/1.49  
% 7.67/1.49  fof(f74,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f35])).
% 7.67/1.49  
% 7.67/1.49  fof(f7,axiom,(
% 7.67/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f60,plain,(
% 7.67/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f7])).
% 7.67/1.49  
% 7.67/1.49  fof(f4,axiom,(
% 7.67/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f44,plain,(
% 7.67/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.67/1.49    inference(nnf_transformation,[],[f4])).
% 7.67/1.49  
% 7.67/1.49  fof(f55,plain,(
% 7.67/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f44])).
% 7.67/1.49  
% 7.67/1.49  fof(f5,axiom,(
% 7.67/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f21,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(ennf_transformation,[],[f5])).
% 7.67/1.49  
% 7.67/1.49  fof(f57,plain,(
% 7.67/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f21])).
% 7.67/1.49  
% 7.67/1.49  fof(f56,plain,(
% 7.67/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f44])).
% 7.67/1.49  
% 7.67/1.49  fof(f84,plain,(
% 7.67/1.49    r1_tarski(sK1,sK0)),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f15,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f32,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f15])).
% 7.67/1.49  
% 7.67/1.49  fof(f33,plain,(
% 7.67/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(flattening,[],[f32])).
% 7.67/1.49  
% 7.67/1.49  fof(f46,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(nnf_transformation,[],[f33])).
% 7.67/1.49  
% 7.67/1.49  fof(f68,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f46])).
% 7.67/1.49  
% 7.67/1.49  fof(f82,plain,(
% 7.67/1.49    v1_funct_2(sK4,sK0,sK3)),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f12,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f28,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f12])).
% 7.67/1.49  
% 7.67/1.49  fof(f65,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f1,axiom,(
% 7.67/1.49    v1_xboole_0(k1_xboole_0)),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f50,plain,(
% 7.67/1.49    v1_xboole_0(k1_xboole_0)),
% 7.67/1.49    inference(cnf_transformation,[],[f1])).
% 7.67/1.49  
% 7.67/1.49  fof(f80,plain,(
% 7.67/1.49    ~v1_xboole_0(sK3)),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f11,axiom,(
% 7.67/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f26,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f11])).
% 7.67/1.49  
% 7.67/1.49  fof(f27,plain,(
% 7.67/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(flattening,[],[f26])).
% 7.67/1.49  
% 7.67/1.49  fof(f64,plain,(
% 7.67/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f27])).
% 7.67/1.49  
% 7.67/1.49  fof(f18,axiom,(
% 7.67/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f38,plain,(
% 7.67/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f18])).
% 7.67/1.49  
% 7.67/1.49  fof(f39,plain,(
% 7.67/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(flattening,[],[f38])).
% 7.67/1.49  
% 7.67/1.49  fof(f79,plain,(
% 7.67/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f39])).
% 7.67/1.49  
% 7.67/1.49  fof(f8,axiom,(
% 7.67/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f23,plain,(
% 7.67/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f8])).
% 7.67/1.49  
% 7.67/1.49  fof(f61,plain,(
% 7.67/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f23])).
% 7.67/1.49  
% 7.67/1.49  fof(f10,axiom,(
% 7.67/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f25,plain,(
% 7.67/1.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f10])).
% 7.67/1.49  
% 7.67/1.49  fof(f63,plain,(
% 7.67/1.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f25])).
% 7.67/1.49  
% 7.67/1.49  fof(f2,axiom,(
% 7.67/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f42,plain,(
% 7.67/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.49    inference(nnf_transformation,[],[f2])).
% 7.67/1.49  
% 7.67/1.49  fof(f43,plain,(
% 7.67/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.49    inference(flattening,[],[f42])).
% 7.67/1.49  
% 7.67/1.49  fof(f53,plain,(
% 7.67/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f43])).
% 7.67/1.49  
% 7.67/1.49  fof(f51,plain,(
% 7.67/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.67/1.49    inference(cnf_transformation,[],[f43])).
% 7.67/1.49  
% 7.67/1.49  fof(f88,plain,(
% 7.67/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.67/1.49    inference(equality_resolution,[],[f51])).
% 7.67/1.49  
% 7.67/1.49  fof(f13,axiom,(
% 7.67/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f29,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f13])).
% 7.67/1.49  
% 7.67/1.49  fof(f66,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f29])).
% 7.67/1.49  
% 7.67/1.49  fof(f85,plain,(
% 7.67/1.49    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f14,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f30,plain,(
% 7.67/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.67/1.49    inference(ennf_transformation,[],[f14])).
% 7.67/1.49  
% 7.67/1.49  fof(f31,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.67/1.49    inference(flattening,[],[f30])).
% 7.67/1.49  
% 7.67/1.49  fof(f67,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f31])).
% 7.67/1.49  
% 7.67/1.49  fof(f70,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f46])).
% 7.67/1.49  
% 7.67/1.49  fof(f86,plain,(
% 7.67/1.49    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f78,plain,(
% 7.67/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f39])).
% 7.67/1.49  
% 7.67/1.49  fof(f3,axiom,(
% 7.67/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f54,plain,(
% 7.67/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f3])).
% 7.67/1.49  
% 7.67/1.49  cnf(c_33,negated_conjecture,
% 7.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 7.67/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1703,plain,
% 7.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_26,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | ~ v1_funct_1(X0)
% 7.67/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.67/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1707,plain,
% 7.67/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.67/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3319,plain,
% 7.67/1.49      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 7.67/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1703,c_1707]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_35,negated_conjecture,
% 7.67/1.49      ( v1_funct_1(sK4) ),
% 7.67/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_38,plain,
% 7.67/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3441,plain,
% 7.67/1.49      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3319,c_38]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_25,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | ~ v1_funct_1(X0)
% 7.67/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1708,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.49      | v1_funct_1(X0) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3233,plain,
% 7.67/1.49      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 7.67/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1703,c_1708]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3330,plain,
% 7.67/1.49      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3233,c_38]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3449,plain,
% 7.67/1.49      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_3441,c_3330]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10,plain,
% 7.67/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1717,plain,
% 7.67/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_6,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1718,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2348,plain,
% 7.67/1.49      ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1703,c_1718]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_5,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_278,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.67/1.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_279,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_278]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_341,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.67/1.49      inference(bin_hyper_res,[status(thm)],[c_7,c_279]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1701,plain,
% 7.67/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.67/1.49      | v1_relat_1(X1) != iProver_top
% 7.67/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4534,plain,
% 7.67/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 7.67/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_2348,c_1701]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4722,plain,
% 7.67/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1717,c_4534]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_32,negated_conjecture,
% 7.67/1.49      ( r1_tarski(sK1,sK0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1704,plain,
% 7.67/1.49      ( r1_tarski(sK1,sK0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23,plain,
% 7.67/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_34,negated_conjecture,
% 7.67/1.49      ( v1_funct_2(sK4,sK0,sK3) ),
% 7.67/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_626,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.49      | sK4 != X0
% 7.67/1.49      | sK3 != X2
% 7.67/1.49      | sK0 != X1
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_627,plain,
% 7.67/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 7.67/1.49      | k1_relset_1(sK0,sK3,sK4) = sK0
% 7.67/1.49      | k1_xboole_0 = sK3 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_626]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_629,plain,
% 7.67/1.49      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_627,c_33]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_15,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1712,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.67/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2603,plain,
% 7.67/1.49      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1703,c_1712]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2711,plain,
% 7.67/1.49      ( k1_relat_1(sK4) = sK0 | sK3 = k1_xboole_0 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_629,c_2603]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_0,plain,
% 7.67/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_36,negated_conjecture,
% 7.67/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.67/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_463,plain,
% 7.67/1.49      ( sK3 != k1_xboole_0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_36]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2918,plain,
% 7.67/1.49      ( k1_relat_1(sK4) = sK0 ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2711,c_463]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_14,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.67/1.49      | ~ v1_relat_1(X1)
% 7.67/1.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.67/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1713,plain,
% 7.67/1.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.67/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.67/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3106,plain,
% 7.67/1.49      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 7.67/1.49      | r1_tarski(X0,sK0) != iProver_top
% 7.67/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_2918,c_1713]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3650,plain,
% 7.67/1.49      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
% 7.67/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1704,c_3106]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4805,plain,
% 7.67/1.49      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_4722,c_3650]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.67/1.49      | ~ v1_funct_1(X0)
% 7.67/1.49      | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1706,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.67/1.49      | v1_funct_1(X0) != iProver_top
% 7.67/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4900,plain,
% 7.67/1.49      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k7_relat_1(sK4,sK1))))) = iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_4805,c_1706]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_11,plain,
% 7.67/1.49      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1716,plain,
% 7.67/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.67/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4803,plain,
% 7.67/1.49      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_4722,c_1716]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4904,plain,
% 7.67/1.49      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)))) = iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_4900,c_4803]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7542,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_4904,c_1718]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_6983,plain,
% 7.67/1.49      ( ~ r1_tarski(k7_relat_1(sK4,sK1),X0)
% 7.67/1.49      | ~ v1_relat_1(X0)
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_341]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8292,plain,
% 7.67/1.49      ( ~ r1_tarski(k7_relat_1(sK4,sK1),sK4)
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1))
% 7.67/1.49      | ~ v1_relat_1(sK4) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_6983]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8293,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
% 7.67/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_8292]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_13,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7711,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,X0),sK4) | ~ v1_relat_1(sK4) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17339,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) | ~ v1_relat_1(sK4) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_7711]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17340,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) = iProver_top
% 7.67/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_17339]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20949,plain,
% 7.67/1.49      ( v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_7542,c_4722,c_8293,c_17340]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20950,plain,
% 7.67/1.49      ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1))) = iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_20949]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.67/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1722,plain,
% 7.67/1.49      ( X0 = X1
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.67/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20954,plain,
% 7.67/1.49      ( k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)) = k7_relat_1(sK4,sK1)
% 7.67/1.49      | r1_tarski(k2_zfmisc_1(sK1,k9_relat_1(sK4,sK1)),k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_20950,c_1722]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1719,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1721,plain,
% 7.67/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.67/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1711,plain,
% 7.67/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.67/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2706,plain,
% 7.67/1.49      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1703,c_1711]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_31,negated_conjecture,
% 7.67/1.49      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 7.67/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1705,plain,
% 7.67/1.49      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2811,plain,
% 7.67/1.49      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_2706,c_1705]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.67/1.49      | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1710,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.67/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.67/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3978,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.67/1.49      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.67/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1710,c_1712]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23196,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 7.67/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,X0) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_4805,c_3978]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23254,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 7.67/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,X0) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(light_normalisation,[status(thm)],[c_23196,c_4805]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23255,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 7.67/1.49      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,X0) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_23254,c_4803]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24488,plain,
% 7.67/1.49      ( r1_tarski(sK1,X0) != iProver_top
% 7.67/1.49      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 7.67/1.49      | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_23255,c_4722,c_8293,c_17340]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24489,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 7.67/1.49      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_24488]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24497,plain,
% 7.67/1.49      ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
% 7.67/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_2811,c_24489]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24511,plain,
% 7.67/1.49      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1721,c_24497]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_21,plain,
% 7.67/1.49      ( v1_funct_2(X0,X1,X2)
% 7.67/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_30,negated_conjecture,
% 7.67/1.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 7.67/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_610,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 7.67/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.67/1.49      | sK2 != X2
% 7.67/1.49      | sK1 != X1
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_611,plain,
% 7.67/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k1_xboole_0 = sK2 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_610]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1694,plain,
% 7.67/1.49      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k1_xboole_0 = sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_40,plain,
% 7.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_612,plain,
% 7.67/1.49      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k1_xboole_0 = sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1780,plain,
% 7.67/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | ~ v1_funct_1(sK4) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1781,plain,
% 7.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 7.67/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1988,plain,
% 7.67/1.49      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | k1_xboole_0 = sK2
% 7.67/1.49      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1694,c_38,c_40,c_612,c_1781]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1989,plain,
% 7.67/1.49      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k1_xboole_0 = sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1988]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3448,plain,
% 7.67/1.49      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
% 7.67/1.49      | sK2 = k1_xboole_0
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_3441,c_1989]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24593,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | sK1 != sK1
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_24511,c_3448]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24818,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.67/1.49      inference(equality_resolution_simp,[status(thm)],[c_24593]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24820,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1719,c_24818]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3211,plain,
% 7.67/1.49      ( r1_tarski(sK1,sK1) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3212,plain,
% 7.67/1.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_3211]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24821,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1710,c_24818]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24822,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,sK1) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(light_normalisation,[status(thm)],[c_24821,c_4805]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24823,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0
% 7.67/1.49      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 7.67/1.49      | r1_tarski(sK1,sK1) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_24822,c_4803]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24827,plain,
% 7.67/1.49      ( sK2 = k1_xboole_0 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_24820,c_2811,c_3212,c_4722,c_8293,c_17340,c_24823]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28,plain,
% 7.67/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.67/1.49      | ~ v1_funct_1(X0)
% 7.67/1.49      | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_637,plain,
% 7.67/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.49      | ~ v1_funct_1(X0)
% 7.67/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | ~ v1_relat_1(X0)
% 7.67/1.49      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 7.67/1.49      | k1_relat_1(X0) != sK1
% 7.67/1.49      | k2_relat_1(X0) != sK2 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_638,plain,
% 7.67/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 7.67/1.49      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_637]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1693,plain,
% 7.67/1.49      ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_639,plain,
% 7.67/1.49      ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2295,plain,
% 7.67/1.49      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
% 7.67/1.49      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1693,c_38,c_40,c_639,c_1781]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2296,plain,
% 7.67/1.49      ( k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 7.67/1.49      | k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK2
% 7.67/1.49      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_2295]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3445,plain,
% 7.67/1.49      ( k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
% 7.67/1.49      | k2_relat_1(k7_relat_1(sK4,sK1)) != sK2
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_3441,c_2296]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4895,plain,
% 7.67/1.49      ( k2_relat_1(k7_relat_1(sK4,sK1)) != sK2
% 7.67/1.49      | sK1 != sK1
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_4805,c_3445]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4896,plain,
% 7.67/1.49      ( k9_relat_1(sK4,sK1) != sK2
% 7.67/1.49      | sK1 != sK1
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_4895,c_4803]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4897,plain,
% 7.67/1.49      ( k9_relat_1(sK4,sK1) != sK2
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(equality_resolution_simp,[status(thm)],[c_4896]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22036,plain,
% 7.67/1.49      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.49      | k9_relat_1(sK4,sK1) != sK2 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_4897,c_4722,c_8293,c_17340]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22037,plain,
% 7.67/1.49      ( k9_relat_1(sK4,sK1) != sK2
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_22036]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24842,plain,
% 7.67/1.49      ( k9_relat_1(sK4,sK1) != k1_xboole_0
% 7.67/1.49      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_24827,c_22037]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24915,plain,
% 7.67/1.49      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_24827,c_2811]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1720,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2609,plain,
% 7.67/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1720,c_1722]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_25417,plain,
% 7.67/1.49      ( k9_relat_1(sK4,sK1) = k1_xboole_0 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_24915,c_2609]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_25891,plain,
% 7.67/1.49      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
% 7.67/1.49      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 7.67/1.49      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_25417,c_4904]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_26389,plain,
% 7.67/1.49      ( v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_20954,c_4722,c_8293,c_17340,c_24842,c_25417,c_25891]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_26393,plain,
% 7.67/1.49      ( $false ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_3449,c_26389]) ).
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  ------                               Statistics
% 7.67/1.49  
% 7.67/1.49  ------ General
% 7.67/1.49  
% 7.67/1.49  abstr_ref_over_cycles:                  0
% 7.67/1.49  abstr_ref_under_cycles:                 0
% 7.67/1.49  gc_basic_clause_elim:                   0
% 7.67/1.49  forced_gc_time:                         0
% 7.67/1.49  parsing_time:                           0.016
% 7.67/1.49  unif_index_cands_time:                  0.
% 7.67/1.49  unif_index_add_time:                    0.
% 7.67/1.49  orderings_time:                         0.
% 7.67/1.49  out_proof_time:                         0.014
% 7.67/1.49  total_time:                             0.763
% 7.67/1.49  num_of_symbols:                         53
% 7.67/1.49  num_of_terms:                           22541
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing
% 7.67/1.49  
% 7.67/1.49  num_of_splits:                          0
% 7.67/1.49  num_of_split_atoms:                     0
% 7.67/1.49  num_of_reused_defs:                     0
% 7.67/1.49  num_eq_ax_congr_red:                    16
% 7.67/1.49  num_of_sem_filtered_clauses:            1
% 7.67/1.49  num_of_subtypes:                        0
% 7.67/1.49  monotx_restored_types:                  0
% 7.67/1.49  sat_num_of_epr_types:                   0
% 7.67/1.49  sat_num_of_non_cyclic_types:            0
% 7.67/1.49  sat_guarded_non_collapsed_types:        0
% 7.67/1.49  num_pure_diseq_elim:                    0
% 7.67/1.49  simp_replaced_by:                       0
% 7.67/1.49  res_preprocessed:                       161
% 7.67/1.49  prep_upred:                             0
% 7.67/1.49  prep_unflattend:                        41
% 7.67/1.49  smt_new_axioms:                         0
% 7.67/1.49  pred_elim_cands:                        4
% 7.67/1.49  pred_elim:                              3
% 7.67/1.49  pred_elim_cl:                           2
% 7.67/1.49  pred_elim_cycles:                       5
% 7.67/1.49  merged_defs:                            8
% 7.67/1.49  merged_defs_ncl:                        0
% 7.67/1.49  bin_hyper_res:                          9
% 7.67/1.49  prep_cycles:                            4
% 7.67/1.49  pred_elim_time:                         0.008
% 7.67/1.49  splitting_time:                         0.
% 7.67/1.49  sem_filter_time:                        0.
% 7.67/1.49  monotx_time:                            0.
% 7.67/1.49  subtype_inf_time:                       0.
% 7.67/1.49  
% 7.67/1.49  ------ Problem properties
% 7.67/1.49  
% 7.67/1.49  clauses:                                33
% 7.67/1.49  conjectures:                            4
% 7.67/1.49  epr:                                    7
% 7.67/1.49  horn:                                   30
% 7.67/1.49  ground:                                 12
% 7.67/1.49  unary:                                  8
% 7.67/1.49  binary:                                 8
% 7.67/1.49  lits:                                   92
% 7.67/1.49  lits_eq:                                30
% 7.67/1.49  fd_pure:                                0
% 7.67/1.49  fd_pseudo:                              0
% 7.67/1.49  fd_cond:                                1
% 7.67/1.49  fd_pseudo_cond:                         1
% 7.67/1.49  ac_symbols:                             0
% 7.67/1.49  
% 7.67/1.49  ------ Propositional Solver
% 7.67/1.49  
% 7.67/1.49  prop_solver_calls:                      33
% 7.67/1.49  prop_fast_solver_calls:                 1822
% 7.67/1.49  smt_solver_calls:                       0
% 7.67/1.49  smt_fast_solver_calls:                  0
% 7.67/1.49  prop_num_of_clauses:                    11077
% 7.67/1.49  prop_preprocess_simplified:             18246
% 7.67/1.49  prop_fo_subsumed:                       60
% 7.67/1.49  prop_solver_time:                       0.
% 7.67/1.49  smt_solver_time:                        0.
% 7.67/1.49  smt_fast_solver_time:                   0.
% 7.67/1.49  prop_fast_solver_time:                  0.
% 7.67/1.49  prop_unsat_core_time:                   0.
% 7.67/1.49  
% 7.67/1.49  ------ QBF
% 7.67/1.49  
% 7.67/1.49  qbf_q_res:                              0
% 7.67/1.49  qbf_num_tautologies:                    0
% 7.67/1.49  qbf_prep_cycles:                        0
% 7.67/1.49  
% 7.67/1.49  ------ BMC1
% 7.67/1.49  
% 7.67/1.49  bmc1_current_bound:                     -1
% 7.67/1.49  bmc1_last_solved_bound:                 -1
% 7.67/1.49  bmc1_unsat_core_size:                   -1
% 7.67/1.49  bmc1_unsat_core_parents_size:           -1
% 7.67/1.49  bmc1_merge_next_fun:                    0
% 7.67/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.49  
% 7.67/1.49  ------ Instantiation
% 7.67/1.49  
% 7.67/1.49  inst_num_of_clauses:                    2748
% 7.67/1.49  inst_num_in_passive:                    269
% 7.67/1.49  inst_num_in_active:                     1584
% 7.67/1.49  inst_num_in_unprocessed:                895
% 7.67/1.49  inst_num_of_loops:                      1700
% 7.67/1.49  inst_num_of_learning_restarts:          0
% 7.67/1.49  inst_num_moves_active_passive:          111
% 7.67/1.49  inst_lit_activity:                      0
% 7.67/1.49  inst_lit_activity_moves:                0
% 7.67/1.49  inst_num_tautologies:                   0
% 7.67/1.49  inst_num_prop_implied:                  0
% 7.67/1.49  inst_num_existing_simplified:           0
% 7.67/1.49  inst_num_eq_res_simplified:             0
% 7.67/1.49  inst_num_child_elim:                    0
% 7.67/1.49  inst_num_of_dismatching_blockings:      1525
% 7.67/1.49  inst_num_of_non_proper_insts:           4780
% 7.67/1.49  inst_num_of_duplicates:                 0
% 7.67/1.49  inst_inst_num_from_inst_to_res:         0
% 7.67/1.49  inst_dismatching_checking_time:         0.
% 7.67/1.49  
% 7.67/1.49  ------ Resolution
% 7.67/1.49  
% 7.67/1.49  res_num_of_clauses:                     0
% 7.67/1.49  res_num_in_passive:                     0
% 7.67/1.49  res_num_in_active:                      0
% 7.67/1.49  res_num_of_loops:                       165
% 7.67/1.49  res_forward_subset_subsumed:            356
% 7.67/1.49  res_backward_subset_subsumed:           0
% 7.67/1.49  res_forward_subsumed:                   0
% 7.67/1.49  res_backward_subsumed:                  0
% 7.67/1.49  res_forward_subsumption_resolution:     0
% 7.67/1.49  res_backward_subsumption_resolution:    0
% 7.67/1.49  res_clause_to_clause_subsumption:       2734
% 7.67/1.49  res_orphan_elimination:                 0
% 7.67/1.49  res_tautology_del:                      357
% 7.67/1.49  res_num_eq_res_simplified:              0
% 7.67/1.49  res_num_sel_changes:                    0
% 7.67/1.49  res_moves_from_active_to_pass:          0
% 7.67/1.49  
% 7.67/1.49  ------ Superposition
% 7.67/1.49  
% 7.67/1.49  sup_time_total:                         0.
% 7.67/1.49  sup_time_generating:                    0.
% 7.67/1.49  sup_time_sim_full:                      0.
% 7.67/1.49  sup_time_sim_immed:                     0.
% 7.67/1.49  
% 7.67/1.49  sup_num_of_clauses:                     770
% 7.67/1.49  sup_num_in_active:                      204
% 7.67/1.49  sup_num_in_passive:                     566
% 7.67/1.49  sup_num_of_loops:                       339
% 7.67/1.49  sup_fw_superposition:                   660
% 7.67/1.49  sup_bw_superposition:                   386
% 7.67/1.49  sup_immediate_simplified:               395
% 7.67/1.49  sup_given_eliminated:                   1
% 7.67/1.49  comparisons_done:                       0
% 7.67/1.49  comparisons_avoided:                    11
% 7.67/1.49  
% 7.67/1.49  ------ Simplifications
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  sim_fw_subset_subsumed:                 55
% 7.67/1.49  sim_bw_subset_subsumed:                 35
% 7.67/1.49  sim_fw_subsumed:                        56
% 7.67/1.49  sim_bw_subsumed:                        7
% 7.67/1.49  sim_fw_subsumption_res:                 0
% 7.67/1.49  sim_bw_subsumption_res:                 0
% 7.67/1.49  sim_tautology_del:                      33
% 7.67/1.49  sim_eq_tautology_del:                   45
% 7.67/1.49  sim_eq_res_simp:                        3
% 7.67/1.49  sim_fw_demodulated:                     184
% 7.67/1.49  sim_bw_demodulated:                     115
% 7.67/1.49  sim_light_normalised:                   172
% 7.67/1.49  sim_joinable_taut:                      0
% 7.67/1.49  sim_joinable_simp:                      0
% 7.67/1.49  sim_ac_normalised:                      0
% 7.67/1.49  sim_smt_subsumption:                    0
% 7.67/1.49  
%------------------------------------------------------------------------------
