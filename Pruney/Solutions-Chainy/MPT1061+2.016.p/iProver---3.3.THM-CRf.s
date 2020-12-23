%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:32 EST 2020

% Result     : Theorem 12.08s
% Output     : CNFRefutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :  303 (8927 expanded)
%              Number of clauses        :  211 (3485 expanded)
%              Number of leaves         :   26 (1950 expanded)
%              Depth                    :   36
%              Number of atoms          :  847 (45530 expanded)
%              Number of equality atoms :  473 (7179 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f43,f51,f50])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f36])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f83,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1504,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1487,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1494,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3527,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1487,c_1494])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1489,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3696,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_1489])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1488,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1495,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2917,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1487,c_1495])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_557,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_33])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_443,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_36])).

cnf(c_861,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1548,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1626,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_860,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1678,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1699,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_443,c_1626,c_1678])).

cnf(c_2920,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2917,c_1699])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1496,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4062,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2920,c_1496])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1499,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2210,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1501])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_265])).

cnf(c_1485,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_2645,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_1485])).

cnf(c_2772,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_2645])).

cnf(c_4283,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4062,c_2772])).

cnf(c_4284,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4283])).

cnf(c_4290,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1488,c_4284])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3955,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1495])).

cnf(c_42837,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_3955])).

cnf(c_42902,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42837,c_4290])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1498,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3256,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2772,c_1498])).

cnf(c_42903,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42902,c_3256])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4394,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4395,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4394])).

cnf(c_43256,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42903,c_2772,c_4395])).

cnf(c_43257,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_43256])).

cnf(c_43262,plain,
    ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3696,c_43257])).

cnf(c_43344,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1504,c_43262])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1490,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4855,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1490])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5034,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4855,c_38])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1480,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_540,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1562,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_1777,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_38,c_40,c_540,c_1562])).

cnf(c_1778,plain,
    ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1777])).

cnf(c_5040,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5034,c_1778])).

cnf(c_43436,plain,
    ( sK2 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43344,c_5040])).

cnf(c_43438,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_43436])).

cnf(c_43440,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_43438])).

cnf(c_2895,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2896,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2895])).

cnf(c_43441,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_43438])).

cnf(c_43442,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_43441,c_4290])).

cnf(c_43443,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43442,c_3256])).

cnf(c_43618,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43440,c_2772,c_2896,c_3696,c_4395,c_43443])).

cnf(c_43874,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43618,c_3696])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1493])).

cnf(c_5637,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_3951])).

cnf(c_5828,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5637,c_3256])).

cnf(c_6735,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5828,c_2772,c_4395])).

cnf(c_6736,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6735])).

cnf(c_6739,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_6736])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2919,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1495])).

cnf(c_8001,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6739,c_2919])).

cnf(c_8004,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8001,c_4290])).

cnf(c_44592,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_43874,c_8004])).

cnf(c_2916,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1495])).

cnf(c_6425,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1504,c_2916])).

cnf(c_6950,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_6425])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1503,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_17,c_14])).

cnf(c_1484,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2371,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1484])).

cnf(c_4740,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_2371])).

cnf(c_2114,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1499])).

cnf(c_6493,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4740,c_2114])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1497,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1505,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3053,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1505])).

cnf(c_3898,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_3053])).

cnf(c_3942,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2114,c_3898])).

cnf(c_6496,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6493,c_3942])).

cnf(c_6951,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6950,c_6,c_6496])).

cnf(c_7995,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6739,c_1501])).

cnf(c_44591,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_43874,c_7995])).

cnf(c_44833,plain,
    ( k7_relat_1(sK4,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44591,c_3053])).

cnf(c_44851,plain,
    ( sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_44592,c_6951,c_44592,c_44833])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_507,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_1482,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_1508,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1482,c_6])).

cnf(c_2060,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_38,c_40,c_1562])).

cnf(c_2061,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2060])).

cnf(c_5037,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5034,c_2061])).

cnf(c_43867,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43618,c_5037])).

cnf(c_43876,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43867,c_5])).

cnf(c_106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_21,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_474,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_475,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_1483,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_1507,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1483,c_5])).

cnf(c_1520,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1507])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1612,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_1708,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_1976,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_2020,plain,
    ( ~ r1_tarski(X0,k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
    | k2_partfun1(sK0,sK3,sK4,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2022,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK3,sK4,sK1))
    | k2_partfun1(sK0,sK3,sK4,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2417,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_2613,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_862,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2517,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X2)
    | X2 != X1
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_4192,plain,
    ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
    | ~ r1_tarski(k7_relat_1(sK4,sK1),X1)
    | X0 != X1
    | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_4194,plain,
    ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4192])).

cnf(c_4350,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8005,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7995])).

cnf(c_13521,plain,
    ( r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_31916,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK4,sK1),X2)
    | X2 != X1
    | k9_relat_1(sK4,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_31918,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k9_relat_1(sK4,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_31916])).

cnf(c_31917,plain,
    ( X0 != X1
    | k9_relat_1(sK4,sK1) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31916])).

cnf(c_31919,plain,
    ( k9_relat_1(sK4,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31917])).

cnf(c_32000,plain,
    ( r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_32001,plain,
    ( r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32000])).

cnf(c_3055,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) = sK2
    | r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_1505])).

cnf(c_3693,plain,
    ( k9_relat_1(sK4,sK1) = sK2
    | r1_tarski(sK2,k9_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_3055])).

cnf(c_43872,plain,
    ( k9_relat_1(sK4,sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43618,c_3693])).

cnf(c_44447,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43876,c_35,c_33,c_106,c_108,c_109,c_111,c_112,c_1520,c_1561,c_1708,c_1976,c_2022,c_2417,c_2613,c_2772,c_2896,c_3696,c_4194,c_4350,c_4395,c_6739,c_8005,c_13521,c_31918,c_31919,c_32001,c_43443,c_43872])).

cnf(c_44853,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44851,c_44447])).

cnf(c_3943,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2772,c_3898])).

cnf(c_3952,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1493])).

cnf(c_6804,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,k1_xboole_0)),X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3943,c_3952])).

cnf(c_6806,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6804,c_3256])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1492,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5049,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5034,c_1492])).

cnf(c_5184,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5049,c_38,c_40])).

cnf(c_5191,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5184,c_1501])).

cnf(c_5471,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5191,c_1485])).

cnf(c_7224,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_5471])).

cnf(c_7226,plain,
    ( v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7224])).

cnf(c_1500,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5822,plain,
    ( m1_subset_1(k7_relat_1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(X0,k1_xboole_0)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_3952])).

cnf(c_32465,plain,
    ( m1_subset_1(k7_relat_1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_5822])).

cnf(c_2297,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1484])).

cnf(c_32493,plain,
    ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32465,c_2297])).

cnf(c_32638,plain,
    ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_32493])).

cnf(c_32797,plain,
    ( k7_relat_1(k7_relat_1(sK4,k1_xboole_0),X0) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2772,c_32638])).

cnf(c_33008,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32797,c_32465])).

cnf(c_33038,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33008,c_32797])).

cnf(c_36542,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6806,c_7226,c_33038])).

cnf(c_36546,plain,
    ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36542,c_1501])).

cnf(c_36588,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_36546,c_3053])).

cnf(c_44920,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_44853,c_36588])).

cnf(c_44921,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44920,c_6951])).

cnf(c_44922,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_44921])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 12.08/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.08/2.00  
% 12.08/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.08/2.00  
% 12.08/2.00  ------  iProver source info
% 12.08/2.00  
% 12.08/2.00  git: date: 2020-06-30 10:37:57 +0100
% 12.08/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.08/2.00  git: non_committed_changes: false
% 12.08/2.00  git: last_make_outside_of_git: false
% 12.08/2.00  
% 12.08/2.00  ------ 
% 12.08/2.00  
% 12.08/2.00  ------ Input Options
% 12.08/2.00  
% 12.08/2.00  --out_options                           all
% 12.08/2.00  --tptp_safe_out                         true
% 12.08/2.00  --problem_path                          ""
% 12.08/2.00  --include_path                          ""
% 12.08/2.00  --clausifier                            res/vclausify_rel
% 12.08/2.00  --clausifier_options                    ""
% 12.08/2.00  --stdin                                 false
% 12.08/2.00  --stats_out                             all
% 12.08/2.00  
% 12.08/2.00  ------ General Options
% 12.08/2.00  
% 12.08/2.00  --fof                                   false
% 12.08/2.00  --time_out_real                         305.
% 12.08/2.00  --time_out_virtual                      -1.
% 12.08/2.00  --symbol_type_check                     false
% 12.08/2.00  --clausify_out                          false
% 12.08/2.00  --sig_cnt_out                           false
% 12.08/2.00  --trig_cnt_out                          false
% 12.08/2.00  --trig_cnt_out_tolerance                1.
% 12.08/2.00  --trig_cnt_out_sk_spl                   false
% 12.08/2.00  --abstr_cl_out                          false
% 12.08/2.00  
% 12.08/2.00  ------ Global Options
% 12.08/2.00  
% 12.08/2.00  --schedule                              default
% 12.08/2.00  --add_important_lit                     false
% 12.08/2.00  --prop_solver_per_cl                    1000
% 12.08/2.00  --min_unsat_core                        false
% 12.08/2.00  --soft_assumptions                      false
% 12.08/2.00  --soft_lemma_size                       3
% 12.08/2.00  --prop_impl_unit_size                   0
% 12.08/2.00  --prop_impl_unit                        []
% 12.08/2.00  --share_sel_clauses                     true
% 12.08/2.00  --reset_solvers                         false
% 12.08/2.00  --bc_imp_inh                            [conj_cone]
% 12.08/2.00  --conj_cone_tolerance                   3.
% 12.08/2.00  --extra_neg_conj                        none
% 12.08/2.00  --large_theory_mode                     true
% 12.08/2.00  --prolific_symb_bound                   200
% 12.08/2.00  --lt_threshold                          2000
% 12.08/2.00  --clause_weak_htbl                      true
% 12.08/2.00  --gc_record_bc_elim                     false
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing Options
% 12.08/2.00  
% 12.08/2.00  --preprocessing_flag                    true
% 12.08/2.00  --time_out_prep_mult                    0.1
% 12.08/2.00  --splitting_mode                        input
% 12.08/2.00  --splitting_grd                         true
% 12.08/2.00  --splitting_cvd                         false
% 12.08/2.00  --splitting_cvd_svl                     false
% 12.08/2.00  --splitting_nvd                         32
% 12.08/2.00  --sub_typing                            true
% 12.08/2.00  --prep_gs_sim                           true
% 12.08/2.00  --prep_unflatten                        true
% 12.08/2.00  --prep_res_sim                          true
% 12.08/2.00  --prep_upred                            true
% 12.08/2.00  --prep_sem_filter                       exhaustive
% 12.08/2.00  --prep_sem_filter_out                   false
% 12.08/2.00  --pred_elim                             true
% 12.08/2.00  --res_sim_input                         true
% 12.08/2.00  --eq_ax_congr_red                       true
% 12.08/2.00  --pure_diseq_elim                       true
% 12.08/2.00  --brand_transform                       false
% 12.08/2.00  --non_eq_to_eq                          false
% 12.08/2.00  --prep_def_merge                        true
% 12.08/2.00  --prep_def_merge_prop_impl              false
% 12.08/2.00  --prep_def_merge_mbd                    true
% 12.08/2.00  --prep_def_merge_tr_red                 false
% 12.08/2.00  --prep_def_merge_tr_cl                  false
% 12.08/2.00  --smt_preprocessing                     true
% 12.08/2.00  --smt_ac_axioms                         fast
% 12.08/2.00  --preprocessed_out                      false
% 12.08/2.00  --preprocessed_stats                    false
% 12.08/2.00  
% 12.08/2.00  ------ Abstraction refinement Options
% 12.08/2.00  
% 12.08/2.00  --abstr_ref                             []
% 12.08/2.00  --abstr_ref_prep                        false
% 12.08/2.00  --abstr_ref_until_sat                   false
% 12.08/2.00  --abstr_ref_sig_restrict                funpre
% 12.08/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.08/2.00  --abstr_ref_under                       []
% 12.08/2.00  
% 12.08/2.00  ------ SAT Options
% 12.08/2.00  
% 12.08/2.00  --sat_mode                              false
% 12.08/2.00  --sat_fm_restart_options                ""
% 12.08/2.00  --sat_gr_def                            false
% 12.08/2.00  --sat_epr_types                         true
% 12.08/2.00  --sat_non_cyclic_types                  false
% 12.08/2.00  --sat_finite_models                     false
% 12.08/2.00  --sat_fm_lemmas                         false
% 12.08/2.00  --sat_fm_prep                           false
% 12.08/2.00  --sat_fm_uc_incr                        true
% 12.08/2.00  --sat_out_model                         small
% 12.08/2.00  --sat_out_clauses                       false
% 12.08/2.00  
% 12.08/2.00  ------ QBF Options
% 12.08/2.00  
% 12.08/2.00  --qbf_mode                              false
% 12.08/2.00  --qbf_elim_univ                         false
% 12.08/2.00  --qbf_dom_inst                          none
% 12.08/2.00  --qbf_dom_pre_inst                      false
% 12.08/2.00  --qbf_sk_in                             false
% 12.08/2.00  --qbf_pred_elim                         true
% 12.08/2.00  --qbf_split                             512
% 12.08/2.00  
% 12.08/2.00  ------ BMC1 Options
% 12.08/2.00  
% 12.08/2.00  --bmc1_incremental                      false
% 12.08/2.00  --bmc1_axioms                           reachable_all
% 12.08/2.00  --bmc1_min_bound                        0
% 12.08/2.00  --bmc1_max_bound                        -1
% 12.08/2.00  --bmc1_max_bound_default                -1
% 12.08/2.00  --bmc1_symbol_reachability              true
% 12.08/2.00  --bmc1_property_lemmas                  false
% 12.08/2.00  --bmc1_k_induction                      false
% 12.08/2.00  --bmc1_non_equiv_states                 false
% 12.08/2.00  --bmc1_deadlock                         false
% 12.08/2.00  --bmc1_ucm                              false
% 12.08/2.00  --bmc1_add_unsat_core                   none
% 12.08/2.00  --bmc1_unsat_core_children              false
% 12.08/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.08/2.00  --bmc1_out_stat                         full
% 12.08/2.00  --bmc1_ground_init                      false
% 12.08/2.00  --bmc1_pre_inst_next_state              false
% 12.08/2.00  --bmc1_pre_inst_state                   false
% 12.08/2.00  --bmc1_pre_inst_reach_state             false
% 12.08/2.00  --bmc1_out_unsat_core                   false
% 12.08/2.00  --bmc1_aig_witness_out                  false
% 12.08/2.00  --bmc1_verbose                          false
% 12.08/2.00  --bmc1_dump_clauses_tptp                false
% 12.08/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.08/2.00  --bmc1_dump_file                        -
% 12.08/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.08/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.08/2.00  --bmc1_ucm_extend_mode                  1
% 12.08/2.00  --bmc1_ucm_init_mode                    2
% 12.08/2.00  --bmc1_ucm_cone_mode                    none
% 12.08/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.08/2.00  --bmc1_ucm_relax_model                  4
% 12.08/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.08/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.08/2.00  --bmc1_ucm_layered_model                none
% 12.08/2.00  --bmc1_ucm_max_lemma_size               10
% 12.08/2.00  
% 12.08/2.00  ------ AIG Options
% 12.08/2.00  
% 12.08/2.00  --aig_mode                              false
% 12.08/2.00  
% 12.08/2.00  ------ Instantiation Options
% 12.08/2.00  
% 12.08/2.00  --instantiation_flag                    true
% 12.08/2.00  --inst_sos_flag                         true
% 12.08/2.00  --inst_sos_phase                        true
% 12.08/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.08/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.08/2.00  --inst_lit_sel_side                     num_symb
% 12.08/2.00  --inst_solver_per_active                1400
% 12.08/2.00  --inst_solver_calls_frac                1.
% 12.08/2.00  --inst_passive_queue_type               priority_queues
% 12.08/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.08/2.00  --inst_passive_queues_freq              [25;2]
% 12.08/2.00  --inst_dismatching                      true
% 12.08/2.00  --inst_eager_unprocessed_to_passive     true
% 12.08/2.00  --inst_prop_sim_given                   true
% 12.08/2.00  --inst_prop_sim_new                     false
% 12.08/2.00  --inst_subs_new                         false
% 12.08/2.00  --inst_eq_res_simp                      false
% 12.08/2.00  --inst_subs_given                       false
% 12.08/2.00  --inst_orphan_elimination               true
% 12.08/2.00  --inst_learning_loop_flag               true
% 12.08/2.00  --inst_learning_start                   3000
% 12.08/2.00  --inst_learning_factor                  2
% 12.08/2.00  --inst_start_prop_sim_after_learn       3
% 12.08/2.00  --inst_sel_renew                        solver
% 12.08/2.00  --inst_lit_activity_flag                true
% 12.08/2.00  --inst_restr_to_given                   false
% 12.08/2.00  --inst_activity_threshold               500
% 12.08/2.00  --inst_out_proof                        true
% 12.08/2.00  
% 12.08/2.00  ------ Resolution Options
% 12.08/2.00  
% 12.08/2.00  --resolution_flag                       true
% 12.08/2.00  --res_lit_sel                           adaptive
% 12.08/2.00  --res_lit_sel_side                      none
% 12.08/2.00  --res_ordering                          kbo
% 12.08/2.00  --res_to_prop_solver                    active
% 12.08/2.00  --res_prop_simpl_new                    false
% 12.08/2.00  --res_prop_simpl_given                  true
% 12.08/2.00  --res_passive_queue_type                priority_queues
% 12.08/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.08/2.00  --res_passive_queues_freq               [15;5]
% 12.08/2.00  --res_forward_subs                      full
% 12.08/2.00  --res_backward_subs                     full
% 12.08/2.00  --res_forward_subs_resolution           true
% 12.08/2.00  --res_backward_subs_resolution          true
% 12.08/2.00  --res_orphan_elimination                true
% 12.08/2.00  --res_time_limit                        2.
% 12.08/2.00  --res_out_proof                         true
% 12.08/2.00  
% 12.08/2.00  ------ Superposition Options
% 12.08/2.00  
% 12.08/2.00  --superposition_flag                    true
% 12.08/2.00  --sup_passive_queue_type                priority_queues
% 12.08/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.08/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.08/2.00  --demod_completeness_check              fast
% 12.08/2.00  --demod_use_ground                      true
% 12.08/2.00  --sup_to_prop_solver                    passive
% 12.08/2.00  --sup_prop_simpl_new                    true
% 12.08/2.00  --sup_prop_simpl_given                  true
% 12.08/2.00  --sup_fun_splitting                     true
% 12.08/2.00  --sup_smt_interval                      50000
% 12.08/2.00  
% 12.08/2.00  ------ Superposition Simplification Setup
% 12.08/2.00  
% 12.08/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.08/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.08/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.08/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.08/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.08/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.08/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.08/2.00  --sup_immed_triv                        [TrivRules]
% 12.08/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_immed_bw_main                     []
% 12.08/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.08/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.08/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_input_bw                          []
% 12.08/2.00  
% 12.08/2.00  ------ Combination Options
% 12.08/2.00  
% 12.08/2.00  --comb_res_mult                         3
% 12.08/2.00  --comb_sup_mult                         2
% 12.08/2.00  --comb_inst_mult                        10
% 12.08/2.00  
% 12.08/2.00  ------ Debug Options
% 12.08/2.00  
% 12.08/2.00  --dbg_backtrace                         false
% 12.08/2.00  --dbg_dump_prop_clauses                 false
% 12.08/2.00  --dbg_dump_prop_clauses_file            -
% 12.08/2.00  --dbg_out_stat                          false
% 12.08/2.00  ------ Parsing...
% 12.08/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.08/2.00  ------ Proving...
% 12.08/2.00  ------ Problem Properties 
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  clauses                                 32
% 12.08/2.00  conjectures                             4
% 12.08/2.00  EPR                                     7
% 12.08/2.00  Horn                                    30
% 12.08/2.00  unary                                   10
% 12.08/2.00  binary                                  8
% 12.08/2.00  lits                                    77
% 12.08/2.00  lits eq                                 27
% 12.08/2.00  fd_pure                                 0
% 12.08/2.00  fd_pseudo                               0
% 12.08/2.00  fd_cond                                 1
% 12.08/2.00  fd_pseudo_cond                          1
% 12.08/2.00  AC symbols                              0
% 12.08/2.00  
% 12.08/2.00  ------ Schedule dynamic 5 is on 
% 12.08/2.00  
% 12.08/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  ------ 
% 12.08/2.00  Current options:
% 12.08/2.00  ------ 
% 12.08/2.00  
% 12.08/2.00  ------ Input Options
% 12.08/2.00  
% 12.08/2.00  --out_options                           all
% 12.08/2.00  --tptp_safe_out                         true
% 12.08/2.00  --problem_path                          ""
% 12.08/2.00  --include_path                          ""
% 12.08/2.00  --clausifier                            res/vclausify_rel
% 12.08/2.00  --clausifier_options                    ""
% 12.08/2.00  --stdin                                 false
% 12.08/2.00  --stats_out                             all
% 12.08/2.00  
% 12.08/2.00  ------ General Options
% 12.08/2.00  
% 12.08/2.00  --fof                                   false
% 12.08/2.00  --time_out_real                         305.
% 12.08/2.00  --time_out_virtual                      -1.
% 12.08/2.00  --symbol_type_check                     false
% 12.08/2.00  --clausify_out                          false
% 12.08/2.00  --sig_cnt_out                           false
% 12.08/2.00  --trig_cnt_out                          false
% 12.08/2.00  --trig_cnt_out_tolerance                1.
% 12.08/2.00  --trig_cnt_out_sk_spl                   false
% 12.08/2.00  --abstr_cl_out                          false
% 12.08/2.00  
% 12.08/2.00  ------ Global Options
% 12.08/2.00  
% 12.08/2.00  --schedule                              default
% 12.08/2.00  --add_important_lit                     false
% 12.08/2.00  --prop_solver_per_cl                    1000
% 12.08/2.00  --min_unsat_core                        false
% 12.08/2.00  --soft_assumptions                      false
% 12.08/2.00  --soft_lemma_size                       3
% 12.08/2.00  --prop_impl_unit_size                   0
% 12.08/2.00  --prop_impl_unit                        []
% 12.08/2.00  --share_sel_clauses                     true
% 12.08/2.00  --reset_solvers                         false
% 12.08/2.00  --bc_imp_inh                            [conj_cone]
% 12.08/2.00  --conj_cone_tolerance                   3.
% 12.08/2.00  --extra_neg_conj                        none
% 12.08/2.00  --large_theory_mode                     true
% 12.08/2.00  --prolific_symb_bound                   200
% 12.08/2.00  --lt_threshold                          2000
% 12.08/2.00  --clause_weak_htbl                      true
% 12.08/2.00  --gc_record_bc_elim                     false
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing Options
% 12.08/2.00  
% 12.08/2.00  --preprocessing_flag                    true
% 12.08/2.00  --time_out_prep_mult                    0.1
% 12.08/2.00  --splitting_mode                        input
% 12.08/2.00  --splitting_grd                         true
% 12.08/2.00  --splitting_cvd                         false
% 12.08/2.00  --splitting_cvd_svl                     false
% 12.08/2.00  --splitting_nvd                         32
% 12.08/2.00  --sub_typing                            true
% 12.08/2.00  --prep_gs_sim                           true
% 12.08/2.00  --prep_unflatten                        true
% 12.08/2.00  --prep_res_sim                          true
% 12.08/2.00  --prep_upred                            true
% 12.08/2.00  --prep_sem_filter                       exhaustive
% 12.08/2.00  --prep_sem_filter_out                   false
% 12.08/2.00  --pred_elim                             true
% 12.08/2.00  --res_sim_input                         true
% 12.08/2.00  --eq_ax_congr_red                       true
% 12.08/2.00  --pure_diseq_elim                       true
% 12.08/2.00  --brand_transform                       false
% 12.08/2.00  --non_eq_to_eq                          false
% 12.08/2.00  --prep_def_merge                        true
% 12.08/2.00  --prep_def_merge_prop_impl              false
% 12.08/2.00  --prep_def_merge_mbd                    true
% 12.08/2.00  --prep_def_merge_tr_red                 false
% 12.08/2.00  --prep_def_merge_tr_cl                  false
% 12.08/2.00  --smt_preprocessing                     true
% 12.08/2.00  --smt_ac_axioms                         fast
% 12.08/2.00  --preprocessed_out                      false
% 12.08/2.00  --preprocessed_stats                    false
% 12.08/2.00  
% 12.08/2.00  ------ Abstraction refinement Options
% 12.08/2.00  
% 12.08/2.00  --abstr_ref                             []
% 12.08/2.00  --abstr_ref_prep                        false
% 12.08/2.00  --abstr_ref_until_sat                   false
% 12.08/2.00  --abstr_ref_sig_restrict                funpre
% 12.08/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.08/2.00  --abstr_ref_under                       []
% 12.08/2.00  
% 12.08/2.00  ------ SAT Options
% 12.08/2.00  
% 12.08/2.00  --sat_mode                              false
% 12.08/2.00  --sat_fm_restart_options                ""
% 12.08/2.00  --sat_gr_def                            false
% 12.08/2.00  --sat_epr_types                         true
% 12.08/2.00  --sat_non_cyclic_types                  false
% 12.08/2.00  --sat_finite_models                     false
% 12.08/2.00  --sat_fm_lemmas                         false
% 12.08/2.00  --sat_fm_prep                           false
% 12.08/2.00  --sat_fm_uc_incr                        true
% 12.08/2.00  --sat_out_model                         small
% 12.08/2.00  --sat_out_clauses                       false
% 12.08/2.00  
% 12.08/2.00  ------ QBF Options
% 12.08/2.00  
% 12.08/2.00  --qbf_mode                              false
% 12.08/2.00  --qbf_elim_univ                         false
% 12.08/2.00  --qbf_dom_inst                          none
% 12.08/2.00  --qbf_dom_pre_inst                      false
% 12.08/2.00  --qbf_sk_in                             false
% 12.08/2.00  --qbf_pred_elim                         true
% 12.08/2.00  --qbf_split                             512
% 12.08/2.00  
% 12.08/2.00  ------ BMC1 Options
% 12.08/2.00  
% 12.08/2.00  --bmc1_incremental                      false
% 12.08/2.00  --bmc1_axioms                           reachable_all
% 12.08/2.00  --bmc1_min_bound                        0
% 12.08/2.00  --bmc1_max_bound                        -1
% 12.08/2.00  --bmc1_max_bound_default                -1
% 12.08/2.00  --bmc1_symbol_reachability              true
% 12.08/2.00  --bmc1_property_lemmas                  false
% 12.08/2.00  --bmc1_k_induction                      false
% 12.08/2.00  --bmc1_non_equiv_states                 false
% 12.08/2.00  --bmc1_deadlock                         false
% 12.08/2.00  --bmc1_ucm                              false
% 12.08/2.00  --bmc1_add_unsat_core                   none
% 12.08/2.00  --bmc1_unsat_core_children              false
% 12.08/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.08/2.00  --bmc1_out_stat                         full
% 12.08/2.00  --bmc1_ground_init                      false
% 12.08/2.00  --bmc1_pre_inst_next_state              false
% 12.08/2.00  --bmc1_pre_inst_state                   false
% 12.08/2.00  --bmc1_pre_inst_reach_state             false
% 12.08/2.00  --bmc1_out_unsat_core                   false
% 12.08/2.00  --bmc1_aig_witness_out                  false
% 12.08/2.00  --bmc1_verbose                          false
% 12.08/2.00  --bmc1_dump_clauses_tptp                false
% 12.08/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.08/2.00  --bmc1_dump_file                        -
% 12.08/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.08/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.08/2.00  --bmc1_ucm_extend_mode                  1
% 12.08/2.00  --bmc1_ucm_init_mode                    2
% 12.08/2.00  --bmc1_ucm_cone_mode                    none
% 12.08/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.08/2.00  --bmc1_ucm_relax_model                  4
% 12.08/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.08/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.08/2.00  --bmc1_ucm_layered_model                none
% 12.08/2.00  --bmc1_ucm_max_lemma_size               10
% 12.08/2.00  
% 12.08/2.00  ------ AIG Options
% 12.08/2.00  
% 12.08/2.00  --aig_mode                              false
% 12.08/2.00  
% 12.08/2.00  ------ Instantiation Options
% 12.08/2.00  
% 12.08/2.00  --instantiation_flag                    true
% 12.08/2.00  --inst_sos_flag                         true
% 12.08/2.00  --inst_sos_phase                        true
% 12.08/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.08/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.08/2.00  --inst_lit_sel_side                     none
% 12.08/2.00  --inst_solver_per_active                1400
% 12.08/2.00  --inst_solver_calls_frac                1.
% 12.08/2.00  --inst_passive_queue_type               priority_queues
% 12.08/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.08/2.00  --inst_passive_queues_freq              [25;2]
% 12.08/2.00  --inst_dismatching                      true
% 12.08/2.00  --inst_eager_unprocessed_to_passive     true
% 12.08/2.00  --inst_prop_sim_given                   true
% 12.08/2.00  --inst_prop_sim_new                     false
% 12.08/2.00  --inst_subs_new                         false
% 12.08/2.00  --inst_eq_res_simp                      false
% 12.08/2.00  --inst_subs_given                       false
% 12.08/2.00  --inst_orphan_elimination               true
% 12.08/2.00  --inst_learning_loop_flag               true
% 12.08/2.00  --inst_learning_start                   3000
% 12.08/2.00  --inst_learning_factor                  2
% 12.08/2.00  --inst_start_prop_sim_after_learn       3
% 12.08/2.00  --inst_sel_renew                        solver
% 12.08/2.00  --inst_lit_activity_flag                true
% 12.08/2.00  --inst_restr_to_given                   false
% 12.08/2.00  --inst_activity_threshold               500
% 12.08/2.00  --inst_out_proof                        true
% 12.08/2.00  
% 12.08/2.00  ------ Resolution Options
% 12.08/2.00  
% 12.08/2.00  --resolution_flag                       false
% 12.08/2.00  --res_lit_sel                           adaptive
% 12.08/2.00  --res_lit_sel_side                      none
% 12.08/2.00  --res_ordering                          kbo
% 12.08/2.00  --res_to_prop_solver                    active
% 12.08/2.00  --res_prop_simpl_new                    false
% 12.08/2.00  --res_prop_simpl_given                  true
% 12.08/2.00  --res_passive_queue_type                priority_queues
% 12.08/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.08/2.00  --res_passive_queues_freq               [15;5]
% 12.08/2.00  --res_forward_subs                      full
% 12.08/2.00  --res_backward_subs                     full
% 12.08/2.00  --res_forward_subs_resolution           true
% 12.08/2.00  --res_backward_subs_resolution          true
% 12.08/2.00  --res_orphan_elimination                true
% 12.08/2.00  --res_time_limit                        2.
% 12.08/2.00  --res_out_proof                         true
% 12.08/2.00  
% 12.08/2.00  ------ Superposition Options
% 12.08/2.00  
% 12.08/2.00  --superposition_flag                    true
% 12.08/2.00  --sup_passive_queue_type                priority_queues
% 12.08/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.08/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.08/2.00  --demod_completeness_check              fast
% 12.08/2.00  --demod_use_ground                      true
% 12.08/2.00  --sup_to_prop_solver                    passive
% 12.08/2.00  --sup_prop_simpl_new                    true
% 12.08/2.00  --sup_prop_simpl_given                  true
% 12.08/2.00  --sup_fun_splitting                     true
% 12.08/2.00  --sup_smt_interval                      50000
% 12.08/2.00  
% 12.08/2.00  ------ Superposition Simplification Setup
% 12.08/2.00  
% 12.08/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.08/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.08/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.08/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.08/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.08/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.08/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.08/2.00  --sup_immed_triv                        [TrivRules]
% 12.08/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_immed_bw_main                     []
% 12.08/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.08/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.08/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.08/2.00  --sup_input_bw                          []
% 12.08/2.00  
% 12.08/2.00  ------ Combination Options
% 12.08/2.00  
% 12.08/2.00  --comb_res_mult                         3
% 12.08/2.00  --comb_sup_mult                         2
% 12.08/2.00  --comb_inst_mult                        10
% 12.08/2.00  
% 12.08/2.00  ------ Debug Options
% 12.08/2.00  
% 12.08/2.00  --dbg_backtrace                         false
% 12.08/2.00  --dbg_dump_prop_clauses                 false
% 12.08/2.00  --dbg_dump_prop_clauses_file            -
% 12.08/2.00  --dbg_out_stat                          false
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  ------ Proving...
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  % SZS status Theorem for theBenchmark.p
% 12.08/2.00  
% 12.08/2.00   Resolution empty clause
% 12.08/2.00  
% 12.08/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.08/2.00  
% 12.08/2.00  fof(f5,axiom,(
% 12.08/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f48,plain,(
% 12.08/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.08/2.00    inference(nnf_transformation,[],[f5])).
% 12.08/2.00  
% 12.08/2.00  fof(f62,plain,(
% 12.08/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f48])).
% 12.08/2.00  
% 12.08/2.00  fof(f2,axiom,(
% 12.08/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f44,plain,(
% 12.08/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.08/2.00    inference(nnf_transformation,[],[f2])).
% 12.08/2.00  
% 12.08/2.00  fof(f45,plain,(
% 12.08/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.08/2.00    inference(flattening,[],[f44])).
% 12.08/2.00  
% 12.08/2.00  fof(f54,plain,(
% 12.08/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.08/2.00    inference(cnf_transformation,[],[f45])).
% 12.08/2.00  
% 12.08/2.00  fof(f91,plain,(
% 12.08/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.08/2.00    inference(equality_resolution,[],[f54])).
% 12.08/2.00  
% 12.08/2.00  fof(f20,conjecture,(
% 12.08/2.00    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f21,negated_conjecture,(
% 12.08/2.00    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 12.08/2.00    inference(negated_conjecture,[],[f20])).
% 12.08/2.00  
% 12.08/2.00  fof(f42,plain,(
% 12.08/2.00    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 12.08/2.00    inference(ennf_transformation,[],[f21])).
% 12.08/2.00  
% 12.08/2.00  fof(f43,plain,(
% 12.08/2.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 12.08/2.00    inference(flattening,[],[f42])).
% 12.08/2.00  
% 12.08/2.00  fof(f51,plain,(
% 12.08/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 12.08/2.00    introduced(choice_axiom,[])).
% 12.08/2.00  
% 12.08/2.00  fof(f50,plain,(
% 12.08/2.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 12.08/2.00    introduced(choice_axiom,[])).
% 12.08/2.00  
% 12.08/2.00  fof(f52,plain,(
% 12.08/2.00    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 12.08/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f43,f51,f50])).
% 12.08/2.00  
% 12.08/2.00  fof(f86,plain,(
% 12.08/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f15,axiom,(
% 12.08/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f33,plain,(
% 12.08/2.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(ennf_transformation,[],[f15])).
% 12.08/2.00  
% 12.08/2.00  fof(f72,plain,(
% 12.08/2.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f33])).
% 12.08/2.00  
% 12.08/2.00  fof(f88,plain,(
% 12.08/2.00    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f87,plain,(
% 12.08/2.00    r1_tarski(sK1,sK0)),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f14,axiom,(
% 12.08/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f32,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(ennf_transformation,[],[f14])).
% 12.08/2.00  
% 12.08/2.00  fof(f71,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f32])).
% 12.08/2.00  
% 12.08/2.00  fof(f17,axiom,(
% 12.08/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f36,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(ennf_transformation,[],[f17])).
% 12.08/2.00  
% 12.08/2.00  fof(f37,plain,(
% 12.08/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(flattening,[],[f36])).
% 12.08/2.00  
% 12.08/2.00  fof(f49,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(nnf_transformation,[],[f37])).
% 12.08/2.00  
% 12.08/2.00  fof(f74,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f49])).
% 12.08/2.00  
% 12.08/2.00  fof(f85,plain,(
% 12.08/2.00    v1_funct_2(sK4,sK0,sK3)),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f1,axiom,(
% 12.08/2.00    v1_xboole_0(k1_xboole_0)),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f53,plain,(
% 12.08/2.00    v1_xboole_0(k1_xboole_0)),
% 12.08/2.00    inference(cnf_transformation,[],[f1])).
% 12.08/2.00  
% 12.08/2.00  fof(f83,plain,(
% 12.08/2.00    ~v1_xboole_0(sK3)),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f12,axiom,(
% 12.08/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f29,plain,(
% 12.08/2.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 12.08/2.00    inference(ennf_transformation,[],[f12])).
% 12.08/2.00  
% 12.08/2.00  fof(f30,plain,(
% 12.08/2.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 12.08/2.00    inference(flattening,[],[f29])).
% 12.08/2.00  
% 12.08/2.00  fof(f69,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f30])).
% 12.08/2.00  
% 12.08/2.00  fof(f8,axiom,(
% 12.08/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f65,plain,(
% 12.08/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f8])).
% 12.08/2.00  
% 12.08/2.00  fof(f61,plain,(
% 12.08/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f48])).
% 12.08/2.00  
% 12.08/2.00  fof(f6,axiom,(
% 12.08/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f23,plain,(
% 12.08/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 12.08/2.00    inference(ennf_transformation,[],[f6])).
% 12.08/2.00  
% 12.08/2.00  fof(f63,plain,(
% 12.08/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f23])).
% 12.08/2.00  
% 12.08/2.00  fof(f16,axiom,(
% 12.08/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f34,plain,(
% 12.08/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 12.08/2.00    inference(ennf_transformation,[],[f16])).
% 12.08/2.00  
% 12.08/2.00  fof(f35,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 12.08/2.00    inference(flattening,[],[f34])).
% 12.08/2.00  
% 12.08/2.00  fof(f73,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f35])).
% 12.08/2.00  
% 12.08/2.00  fof(f9,axiom,(
% 12.08/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f25,plain,(
% 12.08/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.08/2.00    inference(ennf_transformation,[],[f9])).
% 12.08/2.00  
% 12.08/2.00  fof(f66,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f25])).
% 12.08/2.00  
% 12.08/2.00  fof(f7,axiom,(
% 12.08/2.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f24,plain,(
% 12.08/2.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 12.08/2.00    inference(ennf_transformation,[],[f7])).
% 12.08/2.00  
% 12.08/2.00  fof(f64,plain,(
% 12.08/2.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f24])).
% 12.08/2.00  
% 12.08/2.00  fof(f19,axiom,(
% 12.08/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f40,plain,(
% 12.08/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 12.08/2.00    inference(ennf_transformation,[],[f19])).
% 12.08/2.00  
% 12.08/2.00  fof(f41,plain,(
% 12.08/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 12.08/2.00    inference(flattening,[],[f40])).
% 12.08/2.00  
% 12.08/2.00  fof(f82,plain,(
% 12.08/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f41])).
% 12.08/2.00  
% 12.08/2.00  fof(f84,plain,(
% 12.08/2.00    v1_funct_1(sK4)),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f76,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f49])).
% 12.08/2.00  
% 12.08/2.00  fof(f89,plain,(
% 12.08/2.00    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 12.08/2.00    inference(cnf_transformation,[],[f52])).
% 12.08/2.00  
% 12.08/2.00  fof(f18,axiom,(
% 12.08/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f38,plain,(
% 12.08/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 12.08/2.00    inference(ennf_transformation,[],[f18])).
% 12.08/2.00  
% 12.08/2.00  fof(f39,plain,(
% 12.08/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 12.08/2.00    inference(flattening,[],[f38])).
% 12.08/2.00  
% 12.08/2.00  fof(f80,plain,(
% 12.08/2.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f39])).
% 12.08/2.00  
% 12.08/2.00  fof(f4,axiom,(
% 12.08/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f46,plain,(
% 12.08/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.08/2.00    inference(nnf_transformation,[],[f4])).
% 12.08/2.00  
% 12.08/2.00  fof(f47,plain,(
% 12.08/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.08/2.00    inference(flattening,[],[f46])).
% 12.08/2.00  
% 12.08/2.00  fof(f60,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 12.08/2.00    inference(cnf_transformation,[],[f47])).
% 12.08/2.00  
% 12.08/2.00  fof(f92,plain,(
% 12.08/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 12.08/2.00    inference(equality_resolution,[],[f60])).
% 12.08/2.00  
% 12.08/2.00  fof(f59,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 12.08/2.00    inference(cnf_transformation,[],[f47])).
% 12.08/2.00  
% 12.08/2.00  fof(f93,plain,(
% 12.08/2.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 12.08/2.00    inference(equality_resolution,[],[f59])).
% 12.08/2.00  
% 12.08/2.00  fof(f3,axiom,(
% 12.08/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f57,plain,(
% 12.08/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f3])).
% 12.08/2.00  
% 12.08/2.00  fof(f13,axiom,(
% 12.08/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f22,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 12.08/2.00    inference(pure_predicate_removal,[],[f13])).
% 12.08/2.00  
% 12.08/2.00  fof(f31,plain,(
% 12.08/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.08/2.00    inference(ennf_transformation,[],[f22])).
% 12.08/2.00  
% 12.08/2.00  fof(f70,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f31])).
% 12.08/2.00  
% 12.08/2.00  fof(f10,axiom,(
% 12.08/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f26,plain,(
% 12.08/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 12.08/2.00    inference(ennf_transformation,[],[f10])).
% 12.08/2.00  
% 12.08/2.00  fof(f27,plain,(
% 12.08/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.08/2.00    inference(flattening,[],[f26])).
% 12.08/2.00  
% 12.08/2.00  fof(f67,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f27])).
% 12.08/2.00  
% 12.08/2.00  fof(f11,axiom,(
% 12.08/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 12.08/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/2.00  
% 12.08/2.00  fof(f28,plain,(
% 12.08/2.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 12.08/2.00    inference(ennf_transformation,[],[f11])).
% 12.08/2.00  
% 12.08/2.00  fof(f68,plain,(
% 12.08/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f28])).
% 12.08/2.00  
% 12.08/2.00  fof(f56,plain,(
% 12.08/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f45])).
% 12.08/2.00  
% 12.08/2.00  fof(f77,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f49])).
% 12.08/2.00  
% 12.08/2.00  fof(f97,plain,(
% 12.08/2.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 12.08/2.00    inference(equality_resolution,[],[f77])).
% 12.08/2.00  
% 12.08/2.00  fof(f58,plain,(
% 12.08/2.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f47])).
% 12.08/2.00  
% 12.08/2.00  fof(f79,plain,(
% 12.08/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(cnf_transformation,[],[f49])).
% 12.08/2.00  
% 12.08/2.00  fof(f94,plain,(
% 12.08/2.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.08/2.00    inference(equality_resolution,[],[f79])).
% 12.08/2.00  
% 12.08/2.00  fof(f95,plain,(
% 12.08/2.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 12.08/2.00    inference(equality_resolution,[],[f94])).
% 12.08/2.00  
% 12.08/2.00  fof(f81,plain,(
% 12.08/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 12.08/2.00    inference(cnf_transformation,[],[f39])).
% 12.08/2.00  
% 12.08/2.00  cnf(c_8,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.08/2.00      inference(cnf_transformation,[],[f62]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1502,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 12.08/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f91]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1504,plain,
% 12.08/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_33,negated_conjecture,
% 12.08/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 12.08/2.00      inference(cnf_transformation,[],[f86]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1487,plain,
% 12.08/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_19,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 12.08/2.00      inference(cnf_transformation,[],[f72]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1494,plain,
% 12.08/2.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 12.08/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3527,plain,
% 12.08/2.00      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1487,c_1494]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_31,negated_conjecture,
% 12.08/2.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 12.08/2.00      inference(cnf_transformation,[],[f88]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1489,plain,
% 12.08/2.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3696,plain,
% 12.08/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_3527,c_1489]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32,negated_conjecture,
% 12.08/2.00      ( r1_tarski(sK1,sK0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f87]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1488,plain,
% 12.08/2.00      ( r1_tarski(sK1,sK0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_18,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f71]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1495,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 12.08/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2917,plain,
% 12.08/2.00      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1487,c_1495]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_26,plain,
% 12.08/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 12.08/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | k1_relset_1(X1,X2,X0) = X1
% 12.08/2.00      | k1_xboole_0 = X2 ),
% 12.08/2.00      inference(cnf_transformation,[],[f74]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_34,negated_conjecture,
% 12.08/2.00      ( v1_funct_2(sK4,sK0,sK3) ),
% 12.08/2.00      inference(cnf_transformation,[],[f85]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_554,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | k1_relset_1(X1,X2,X0) = X1
% 12.08/2.00      | sK4 != X0
% 12.08/2.00      | sK3 != X2
% 12.08/2.00      | sK0 != X1
% 12.08/2.00      | k1_xboole_0 = X2 ),
% 12.08/2.00      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_555,plain,
% 12.08/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 12.08/2.00      | k1_relset_1(sK0,sK3,sK4) = sK0
% 12.08/2.00      | k1_xboole_0 = sK3 ),
% 12.08/2.00      inference(unflattening,[status(thm)],[c_554]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_557,plain,
% 12.08/2.00      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 12.08/2.00      inference(global_propositional_subsumption,[status(thm)],[c_555,c_33]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_0,plain,
% 12.08/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f53]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_36,negated_conjecture,
% 12.08/2.00      ( ~ v1_xboole_0(sK3) ),
% 12.08/2.00      inference(cnf_transformation,[],[f83]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_443,plain,
% 12.08/2.00      ( sK3 != k1_xboole_0 ),
% 12.08/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_36]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_861,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1548,plain,
% 12.08/2.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_861]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1626,plain,
% 12.08/2.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_1548]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_860,plain,( X0 = X0 ),theory(equality) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1678,plain,
% 12.08/2.00      ( sK3 = sK3 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_860]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1699,plain,
% 12.08/2.00      ( k1_relset_1(sK0,sK3,sK4) = sK0 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_557,c_443,c_1626,c_1678]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2920,plain,
% 12.08/2.00      ( k1_relat_1(sK4) = sK0 ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_2917,c_1699]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_16,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 12.08/2.00      | ~ v1_relat_1(X1)
% 12.08/2.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f69]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1496,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 12.08/2.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4062,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 12.08/2.00      | r1_tarski(X0,sK0) != iProver_top
% 12.08/2.00      | v1_relat_1(sK4) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2920,c_1496]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_12,plain,
% 12.08/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 12.08/2.00      inference(cnf_transformation,[],[f65]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1499,plain,
% 12.08/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_9,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 12.08/2.00      inference(cnf_transformation,[],[f61]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1501,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.08/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2210,plain,
% 12.08/2.00      ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1487,c_1501]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_10,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f63]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_264,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 12.08/2.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_265,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_264]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_327,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 12.08/2.00      inference(bin_hyper_res,[status(thm)],[c_10,c_265]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1485,plain,
% 12.08/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.08/2.00      | v1_relat_1(X1) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2645,plain,
% 12.08/2.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 12.08/2.00      | v1_relat_1(sK4) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2210,c_1485]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2772,plain,
% 12.08/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1499,c_2645]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4283,plain,
% 12.08/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 12.08/2.00      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 12.08/2.00      inference(global_propositional_subsumption,[status(thm)],[c_4062,c_2772]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4284,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 12.08/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_4283]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4290,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1488,c_4284]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_20,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 12.08/2.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 12.08/2.00      | ~ v1_relat_1(X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f73]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1493,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 12.08/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3955,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 12.08/2.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 12.08/2.00      | v1_relat_1(X2) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1493,c_1495]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_42837,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_4290,c_3955]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_42902,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),X1) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_42837,c_4290]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_13,plain,
% 12.08/2.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 12.08/2.00      inference(cnf_transformation,[],[f66]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1498,plain,
% 12.08/2.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3256,plain,
% 12.08/2.00      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2772,c_1498]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_42903,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_42902,c_3256]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_11,plain,
% 12.08/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 12.08/2.00      inference(cnf_transformation,[],[f64]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4394,plain,
% 12.08/2.00      ( v1_relat_1(k7_relat_1(sK4,sK1)) | ~ v1_relat_1(sK4) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4395,plain,
% 12.08/2.00      ( v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
% 12.08/2.00      | v1_relat_1(sK4) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_4394]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43256,plain,
% 12.08/2.00      ( r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 12.08/2.00      | k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_42903,c_2772,c_4395]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43257,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,sK1)) = sK1
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X1) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_43256]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43262,plain,
% 12.08/2.00      ( k1_relset_1(X0,sK2,k7_relat_1(sK4,sK1)) = sK1
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_3696,c_43257]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43344,plain,
% 12.08/2.00      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1504,c_43262]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_29,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ v1_funct_1(X0)
% 12.08/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 12.08/2.00      inference(cnf_transformation,[],[f82]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1490,plain,
% 12.08/2.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 12.08/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.08/2.00      | v1_funct_1(X2) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4855,plain,
% 12.08/2.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 12.08/2.00      | v1_funct_1(sK4) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1487,c_1490]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_35,negated_conjecture,
% 12.08/2.00      ( v1_funct_1(sK4) ),
% 12.08/2.00      inference(cnf_transformation,[],[f84]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_38,plain,
% 12.08/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5034,plain,
% 12.08/2.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 12.08/2.00      inference(global_propositional_subsumption,[status(thm)],[c_4855,c_38]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_24,plain,
% 12.08/2.00      ( v1_funct_2(X0,X1,X2)
% 12.08/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | k1_relset_1(X1,X2,X0) != X1
% 12.08/2.00      | k1_xboole_0 = X2 ),
% 12.08/2.00      inference(cnf_transformation,[],[f76]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_30,negated_conjecture,
% 12.08/2.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 12.08/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 12.08/2.00      inference(cnf_transformation,[],[f89]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_538,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 12.08/2.00      | k1_relset_1(X1,X2,X0) != X1
% 12.08/2.00      | sK2 != X2
% 12.08/2.00      | sK1 != X1
% 12.08/2.00      | k1_xboole_0 = X2 ),
% 12.08/2.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_539,plain,
% 12.08/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 12.08/2.00      | k1_xboole_0 = sK2 ),
% 12.08/2.00      inference(unflattening,[status(thm)],[c_538]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1480,plain,
% 12.08/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 12.08/2.00      | k1_xboole_0 = sK2
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_40,plain,
% 12.08/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_540,plain,
% 12.08/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 12.08/2.00      | k1_xboole_0 = sK2
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_28,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ v1_funct_1(X0)
% 12.08/2.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 12.08/2.00      inference(cnf_transformation,[],[f80]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1561,plain,
% 12.08/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | ~ v1_funct_1(sK4) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_28]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1562,plain,
% 12.08/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 12.08/2.00      | v1_funct_1(sK4) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1777,plain,
% 12.08/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | k1_xboole_0 = sK2
% 12.08/2.00      | k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_1480,c_38,c_40,c_540,c_1562]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1778,plain,
% 12.08/2.00      ( k1_relset_1(sK1,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 12.08/2.00      | k1_xboole_0 = sK2
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_1777]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5040,plain,
% 12.08/2.00      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) != sK1
% 12.08/2.00      | sK2 = k1_xboole_0
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_5034,c_1778]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43436,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | sK1 != sK1
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43344,c_5040]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43438,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 12.08/2.00      inference(equality_resolution_simp,[status(thm)],[c_43436]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43440,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1502,c_43438]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2895,plain,
% 12.08/2.00      ( r1_tarski(sK1,sK1) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2896,plain,
% 12.08/2.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_2895]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43441,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1493,c_43438]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43442,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_43441,c_4290]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43443,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43442,c_3256]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43618,plain,
% 12.08/2.00      ( sK2 = k1_xboole_0 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_43440,c_2772,c_2896,c_3696,c_4395,c_43443]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43874,plain,
% 12.08/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43618,c_3696]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5,plain,
% 12.08/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f92]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3951,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5,c_1493]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5637,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),k1_xboole_0) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_4290,c_3951]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5828,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_5637,c_3256]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6735,plain,
% 12.08/2.00      ( r1_tarski(sK1,X0) != iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_5828,c_2772,c_4395]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6736,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 12.08/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_6735]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6739,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1504,c_6736]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6,plain,
% 12.08/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f93]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2919,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 12.08/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_6,c_1495]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_8001,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1))
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_6739,c_2919]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_8004,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_8001,c_4290]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44592,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK4,sK1)) = sK1 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_43874,c_8004]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2916,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 12.08/2.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1502,c_1495]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6425,plain,
% 12.08/2.00      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1504,c_2916]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6950,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_6,c_6425]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f57]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1503,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_17,plain,
% 12.08/2.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 12.08/2.00      inference(cnf_transformation,[],[f70]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_14,plain,
% 12.08/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f67]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_448,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ v1_relat_1(X0)
% 12.08/2.00      | k7_relat_1(X0,X1) = X0 ),
% 12.08/2.00      inference(resolution,[status(thm)],[c_17,c_14]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1484,plain,
% 12.08/2.00      ( k7_relat_1(X0,X1) = X0
% 12.08/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2371,plain,
% 12.08/2.00      ( k7_relat_1(X0,X1) = X0
% 12.08/2.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1502,c_1484]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4740,plain,
% 12.08/2.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 12.08/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1503,c_2371]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2114,plain,
% 12.08/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5,c_1499]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6493,plain,
% 12.08/2.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.08/2.00      inference(global_propositional_subsumption,[status(thm)],[c_4740,c_2114]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_15,plain,
% 12.08/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f68]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1497,plain,
% 12.08/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 12.08/2.00      inference(cnf_transformation,[],[f56]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1505,plain,
% 12.08/2.00      ( X0 = X1
% 12.08/2.00      | r1_tarski(X0,X1) != iProver_top
% 12.08/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3053,plain,
% 12.08/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1503,c_1505]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3898,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1497,c_3053]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3942,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2114,c_3898]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6496,plain,
% 12.08/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_6493,c_3942]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6951,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_6950,c_6,c_6496]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_7995,plain,
% 12.08/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 12.08/2.00      | r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_6739,c_1501]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44591,plain,
% 12.08/2.00      ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_43874,c_7995]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44833,plain,
% 12.08/2.00      ( k7_relat_1(sK4,sK1) = k1_xboole_0 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_44591,c_3053]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44851,plain,
% 12.08/2.00      ( sK1 = k1_xboole_0 ),
% 12.08/2.00      inference(light_normalisation,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_44592,c_6951,c_44592,c_44833]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_23,plain,
% 12.08/2.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 12.08/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 12.08/2.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f97]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_506,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 12.08/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 12.08/2.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 12.08/2.00      | sK2 != X1
% 12.08/2.00      | sK1 != k1_xboole_0 ),
% 12.08/2.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_507,plain,
% 12.08/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0 ),
% 12.08/2.00      inference(unflattening,[status(thm)],[c_506]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1482,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1508,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_1482,c_6]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2060,plain,
% 12.08/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_1508,c_38,c_40,c_1562]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2061,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK0,sK3,sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(renaming,[status(thm)],[c_2060]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5037,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_5034,c_2061]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43867,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43618,c_5037]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43876,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0
% 12.08/2.00      | sK1 != k1_xboole_0
% 12.08/2.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43867,c_5]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_106,plain,
% 12.08/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 12.08/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_7,plain,
% 12.08/2.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 = X1
% 12.08/2.00      | k1_xboole_0 = X0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f58]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_108,plain,
% 12.08/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_109,plain,
% 12.08/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_111,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_110,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_112,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_110]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_21,plain,
% 12.08/2.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 12.08/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 12.08/2.00      | k1_xboole_0 = X0 ),
% 12.08/2.00      inference(cnf_transformation,[],[f95]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_474,plain,
% 12.08/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | sK2 != k1_xboole_0
% 12.08/2.00      | sK1 != X0
% 12.08/2.00      | k1_xboole_0 = X0 ),
% 12.08/2.00      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_475,plain,
% 12.08/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | sK2 != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 = sK1 ),
% 12.08/2.00      inference(unflattening,[status(thm)],[c_474]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1483,plain,
% 12.08/2.00      ( k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | sK2 != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 = sK1
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1507,plain,
% 12.08/2.00      ( k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | sK2 != k1_xboole_0
% 12.08/2.00      | sK1 = k1_xboole_0
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 12.08/2.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_1483,c_5]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1520,plain,
% 12.08/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 12.08/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | sK2 != k1_xboole_0
% 12.08/2.00      | sK1 = k1_xboole_0 ),
% 12.08/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1507]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_865,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.08/2.00      theory(equality) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1612,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,X1)
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 12.08/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != X1 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_865]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1706,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 12.08/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_1612]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1708,plain,
% 12.08/2.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 12.08/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_1706]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1976,plain,
% 12.08/2.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_860]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2020,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) = X0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2022,plain,
% 12.08/2.00      ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k1_xboole_0)
% 12.08/2.00      | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK3,sK4,sK1))
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) = k1_xboole_0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_2020]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2415,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2417,plain,
% 12.08/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 12.08/2.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_2415]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2613,plain,
% 12.08/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 12.08/2.00      | ~ v1_funct_1(sK4)
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_29]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_862,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.08/2.00      theory(equality) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2517,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1)
% 12.08/2.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X2)
% 12.08/2.00      | X2 != X1
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_862]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4192,plain,
% 12.08/2.00      ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
% 12.08/2.00      | ~ r1_tarski(k7_relat_1(sK4,sK1),X1)
% 12.08/2.00      | X0 != X1
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_2517]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4194,plain,
% 12.08/2.00      ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k1_xboole_0)
% 12.08/2.00      | ~ r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
% 12.08/2.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
% 12.08/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_4192]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_4350,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_8005,plain,
% 12.08/2.00      ( ~ r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
% 12.08/2.00      | r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) ),
% 12.08/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_7995]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_13521,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_31916,plain,
% 12.08/2.00      ( ~ r1_tarski(X0,X1)
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X2)
% 12.08/2.00      | X2 != X1
% 12.08/2.00      | k9_relat_1(sK4,sK1) != X0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_862]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_31918,plain,
% 12.08/2.00      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
% 12.08/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 12.08/2.00      | k9_relat_1(sK4,sK1) != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_31916]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_31917,plain,
% 12.08/2.00      ( X0 != X1
% 12.08/2.00      | k9_relat_1(sK4,sK1) != X2
% 12.08/2.00      | r1_tarski(X2,X1) != iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),X0) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_31916]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_31919,plain,
% 12.08/2.00      ( k9_relat_1(sK4,sK1) != k1_xboole_0
% 12.08/2.00      | k1_xboole_0 != k1_xboole_0
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top
% 12.08/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_31917]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32000,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32001,plain,
% 12.08/2.00      ( r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_32000]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3055,plain,
% 12.08/2.00      ( k7_relset_1(sK0,sK3,sK4,sK1) = sK2
% 12.08/2.00      | r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1489,c_1505]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3693,plain,
% 12.08/2.00      ( k9_relat_1(sK4,sK1) = sK2
% 12.08/2.00      | r1_tarski(sK2,k9_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_3527,c_3055]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_43872,plain,
% 12.08/2.00      ( k9_relat_1(sK4,sK1) = k1_xboole_0
% 12.08/2.00      | r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_43618,c_3693]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44447,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK1)) != k1_xboole_0 ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_43876,c_35,c_33,c_106,c_108,c_109,c_111,c_112,c_1520,
% 12.08/2.00                 c_1561,c_1708,c_1976,c_2022,c_2417,c_2613,c_2772,c_2896,
% 12.08/2.00                 c_3696,c_4194,c_4350,c_4395,c_6739,c_8005,c_13521,c_31918,
% 12.08/2.00                 c_31919,c_32001,c_43443,c_43872]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44853,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) != k1_xboole_0 ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_44851,c_44447]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3943,plain,
% 12.08/2.00      ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2772,c_3898]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_3952,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_6,c_1493]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6804,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,k1_xboole_0)),X0) != iProver_top
% 12.08/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_3943,c_3952]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_6806,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k9_relat_1(sK4,k1_xboole_0),X0) != iProver_top
% 12.08/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_6804,c_3256]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_27,plain,
% 12.08/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.08/2.00      | ~ v1_funct_1(X0) ),
% 12.08/2.00      inference(cnf_transformation,[],[f81]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1492,plain,
% 12.08/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 12.08/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 12.08/2.00      | v1_funct_1(X0) != iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5049,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 12.08/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 12.08/2.00      | v1_funct_1(sK4) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5034,c_1492]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5184,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_5049,c_38,c_40]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5191,plain,
% 12.08/2.00      ( r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5184,c_1501]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5471,plain,
% 12.08/2.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 12.08/2.00      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5191,c_1485]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_7224,plain,
% 12.08/2.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1499,c_5471]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_7226,plain,
% 12.08/2.00      ( v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 12.08/2.00      inference(instantiation,[status(thm)],[c_7224]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_1500,plain,
% 12.08/2.00      ( v1_relat_1(X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 12.08/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_5822,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | r1_tarski(k2_relat_1(k7_relat_1(X0,k1_xboole_0)),X1) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1497,c_3952]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32465,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1504,c_5822]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_2297,plain,
% 12.08/2.00      ( k7_relat_1(X0,X1) = X0
% 12.08/2.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_5,c_1484]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32493,plain,
% 12.08/2.00      ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
% 12.08/2.00      | v1_relat_1(X0) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(X0,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_32465,c_2297]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32638,plain,
% 12.08/2.00      ( k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) = k7_relat_1(X0,k1_xboole_0)
% 12.08/2.00      | v1_relat_1(X0) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_1500,c_32493]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_32797,plain,
% 12.08/2.00      ( k7_relat_1(k7_relat_1(sK4,k1_xboole_0),X0) = k7_relat_1(sK4,k1_xboole_0) ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_2772,c_32638]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_33008,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)) != iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_32797,c_32465]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_33038,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 12.08/2.00      | v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_33008,c_32797]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_36542,plain,
% 12.08/2.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 12.08/2.00      inference(global_propositional_subsumption,
% 12.08/2.00                [status(thm)],
% 12.08/2.00                [c_6806,c_7226,c_33038]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_36546,plain,
% 12.08/2.00      ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_36542,c_1501]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_36588,plain,
% 12.08/2.00      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 12.08/2.00      inference(superposition,[status(thm)],[c_36546,c_3053]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44920,plain,
% 12.08/2.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 12.08/2.00      inference(light_normalisation,[status(thm)],[c_44853,c_36588]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44921,plain,
% 12.08/2.00      ( k1_xboole_0 != k1_xboole_0 ),
% 12.08/2.00      inference(demodulation,[status(thm)],[c_44920,c_6951]) ).
% 12.08/2.00  
% 12.08/2.00  cnf(c_44922,plain,
% 12.08/2.00      ( $false ),
% 12.08/2.00      inference(equality_resolution_simp,[status(thm)],[c_44921]) ).
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.08/2.00  
% 12.08/2.00  ------                               Statistics
% 12.08/2.00  
% 12.08/2.00  ------ General
% 12.08/2.00  
% 12.08/2.00  abstr_ref_over_cycles:                  0
% 12.08/2.00  abstr_ref_under_cycles:                 0
% 12.08/2.00  gc_basic_clause_elim:                   0
% 12.08/2.00  forced_gc_time:                         0
% 12.08/2.00  parsing_time:                           0.016
% 12.08/2.00  unif_index_cands_time:                  0.
% 12.08/2.00  unif_index_add_time:                    0.
% 12.08/2.00  orderings_time:                         0.
% 12.08/2.00  out_proof_time:                         0.024
% 12.08/2.00  total_time:                             1.463
% 12.08/2.00  num_of_symbols:                         53
% 12.08/2.00  num_of_terms:                           45242
% 12.08/2.00  
% 12.08/2.00  ------ Preprocessing
% 12.08/2.00  
% 12.08/2.00  num_of_splits:                          0
% 12.08/2.00  num_of_split_atoms:                     0
% 12.08/2.00  num_of_reused_defs:                     0
% 12.08/2.00  num_eq_ax_congr_red:                    16
% 12.08/2.00  num_of_sem_filtered_clauses:            1
% 12.08/2.00  num_of_subtypes:                        0
% 12.08/2.00  monotx_restored_types:                  0
% 12.08/2.00  sat_num_of_epr_types:                   0
% 12.08/2.00  sat_num_of_non_cyclic_types:            0
% 12.08/2.00  sat_guarded_non_collapsed_types:        0
% 12.08/2.00  num_pure_diseq_elim:                    0
% 12.08/2.00  simp_replaced_by:                       0
% 12.08/2.00  res_preprocessed:                       159
% 12.08/2.00  prep_upred:                             0
% 12.08/2.00  prep_unflattend:                        33
% 12.08/2.00  smt_new_axioms:                         0
% 12.08/2.00  pred_elim_cands:                        4
% 12.08/2.00  pred_elim:                              3
% 12.08/2.00  pred_elim_cl:                           4
% 12.08/2.00  pred_elim_cycles:                       5
% 12.08/2.00  merged_defs:                            8
% 12.08/2.00  merged_defs_ncl:                        0
% 12.08/2.00  bin_hyper_res:                          9
% 12.08/2.00  prep_cycles:                            4
% 12.08/2.00  pred_elim_time:                         0.005
% 12.08/2.00  splitting_time:                         0.
% 12.08/2.00  sem_filter_time:                        0.
% 12.08/2.00  monotx_time:                            0.001
% 12.08/2.00  subtype_inf_time:                       0.
% 12.08/2.00  
% 12.08/2.00  ------ Problem properties
% 12.08/2.00  
% 12.08/2.00  clauses:                                32
% 12.08/2.00  conjectures:                            4
% 12.08/2.00  epr:                                    7
% 12.08/2.00  horn:                                   30
% 12.08/2.00  ground:                                 11
% 12.08/2.00  unary:                                  10
% 12.08/2.00  binary:                                 8
% 12.08/2.00  lits:                                   77
% 12.08/2.00  lits_eq:                                27
% 12.08/2.00  fd_pure:                                0
% 12.08/2.00  fd_pseudo:                              0
% 12.08/2.00  fd_cond:                                1
% 12.08/2.00  fd_pseudo_cond:                         1
% 12.08/2.00  ac_symbols:                             0
% 12.08/2.00  
% 12.08/2.00  ------ Propositional Solver
% 12.08/2.00  
% 12.08/2.00  prop_solver_calls:                      43
% 12.08/2.00  prop_fast_solver_calls:                 2566
% 12.08/2.00  smt_solver_calls:                       0
% 12.08/2.00  smt_fast_solver_calls:                  0
% 12.08/2.00  prop_num_of_clauses:                    20057
% 12.08/2.00  prop_preprocess_simplified:             35578
% 12.08/2.00  prop_fo_subsumed:                       97
% 12.08/2.00  prop_solver_time:                       0.
% 12.08/2.00  smt_solver_time:                        0.
% 12.08/2.00  smt_fast_solver_time:                   0.
% 12.08/2.00  prop_fast_solver_time:                  0.
% 12.08/2.00  prop_unsat_core_time:                   0.
% 12.08/2.00  
% 12.08/2.00  ------ QBF
% 12.08/2.00  
% 12.08/2.00  qbf_q_res:                              0
% 12.08/2.00  qbf_num_tautologies:                    0
% 12.08/2.00  qbf_prep_cycles:                        0
% 12.08/2.00  
% 12.08/2.00  ------ BMC1
% 12.08/2.00  
% 12.08/2.00  bmc1_current_bound:                     -1
% 12.08/2.00  bmc1_last_solved_bound:                 -1
% 12.08/2.00  bmc1_unsat_core_size:                   -1
% 12.08/2.00  bmc1_unsat_core_parents_size:           -1
% 12.08/2.00  bmc1_merge_next_fun:                    0
% 12.08/2.00  bmc1_unsat_core_clauses_time:           0.
% 12.08/2.00  
% 12.08/2.00  ------ Instantiation
% 12.08/2.00  
% 12.08/2.00  inst_num_of_clauses:                    603
% 12.08/2.00  inst_num_in_passive:                    111
% 12.08/2.00  inst_num_in_active:                     3177
% 12.08/2.00  inst_num_in_unprocessed:                185
% 12.08/2.00  inst_num_of_loops:                      3309
% 12.08/2.00  inst_num_of_learning_restarts:          1
% 12.08/2.00  inst_num_moves_active_passive:          125
% 12.08/2.00  inst_lit_activity:                      0
% 12.08/2.00  inst_lit_activity_moves:                0
% 12.08/2.00  inst_num_tautologies:                   0
% 12.08/2.00  inst_num_prop_implied:                  0
% 12.08/2.00  inst_num_existing_simplified:           0
% 12.08/2.00  inst_num_eq_res_simplified:             0
% 12.08/2.00  inst_num_child_elim:                    0
% 12.08/2.00  inst_num_of_dismatching_blockings:      2701
% 12.08/2.00  inst_num_of_non_proper_insts:           9375
% 12.08/2.00  inst_num_of_duplicates:                 0
% 12.08/2.00  inst_inst_num_from_inst_to_res:         0
% 12.08/2.00  inst_dismatching_checking_time:         0.
% 12.08/2.00  
% 12.08/2.00  ------ Resolution
% 12.08/2.00  
% 12.08/2.00  res_num_of_clauses:                     45
% 12.08/2.00  res_num_in_passive:                     45
% 12.08/2.00  res_num_in_active:                      0
% 12.08/2.00  res_num_of_loops:                       163
% 12.08/2.00  res_forward_subset_subsumed:            555
% 12.08/2.00  res_backward_subset_subsumed:           0
% 12.08/2.00  res_forward_subsumed:                   0
% 12.08/2.00  res_backward_subsumed:                  0
% 12.08/2.00  res_forward_subsumption_resolution:     0
% 12.08/2.00  res_backward_subsumption_resolution:    0
% 12.08/2.00  res_clause_to_clause_subsumption:       9710
% 12.08/2.00  res_orphan_elimination:                 0
% 12.08/2.00  res_tautology_del:                      547
% 12.08/2.00  res_num_eq_res_simplified:              0
% 12.08/2.00  res_num_sel_changes:                    0
% 12.08/2.00  res_moves_from_active_to_pass:          0
% 12.08/2.00  
% 12.08/2.00  ------ Superposition
% 12.08/2.00  
% 12.08/2.00  sup_time_total:                         0.
% 12.08/2.00  sup_time_generating:                    0.
% 12.08/2.00  sup_time_sim_full:                      0.
% 12.08/2.00  sup_time_sim_immed:                     0.
% 12.08/2.00  
% 12.08/2.00  sup_num_of_clauses:                     1430
% 12.08/2.00  sup_num_in_active:                      277
% 12.08/2.00  sup_num_in_passive:                     1153
% 12.08/2.00  sup_num_of_loops:                       661
% 12.08/2.00  sup_fw_superposition:                   2021
% 12.08/2.00  sup_bw_superposition:                   705
% 12.08/2.00  sup_immediate_simplified:               1083
% 12.08/2.00  sup_given_eliminated:                   11
% 12.08/2.00  comparisons_done:                       0
% 12.08/2.00  comparisons_avoided:                    0
% 12.08/2.00  
% 12.08/2.00  ------ Simplifications
% 12.08/2.00  
% 12.08/2.00  
% 12.08/2.00  sim_fw_subset_subsumed:                 66
% 12.08/2.00  sim_bw_subset_subsumed:                 129
% 12.08/2.00  sim_fw_subsumed:                        179
% 12.08/2.00  sim_bw_subsumed:                        79
% 12.08/2.00  sim_fw_subsumption_res:                 0
% 12.08/2.00  sim_bw_subsumption_res:                 0
% 12.08/2.00  sim_tautology_del:                      65
% 12.08/2.00  sim_eq_tautology_del:                   307
% 12.08/2.00  sim_eq_res_simp:                        2
% 12.08/2.00  sim_fw_demodulated:                     596
% 12.08/2.00  sim_bw_demodulated:                     346
% 12.08/2.00  sim_light_normalised:                   482
% 12.08/2.00  sim_joinable_taut:                      0
% 12.08/2.00  sim_joinable_simp:                      0
% 12.08/2.00  sim_ac_normalised:                      0
% 12.08/2.00  sim_smt_subsumption:                    0
% 12.08/2.00  
%------------------------------------------------------------------------------
