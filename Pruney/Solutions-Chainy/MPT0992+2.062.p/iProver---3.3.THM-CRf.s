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
% DateTime   : Thu Dec  3 12:03:59 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  303 (3285 expanded)
%              Number of clauses        :  195 (1360 expanded)
%              Number of leaves         :   30 ( 589 expanded)
%              Depth                    :   31
%              Number of atoms          :  877 (14458 expanded)
%              Number of equality atoms :  442 (4180 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f74,plain,
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

fof(f75,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f74])).

fof(f122,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f26,axiom,(
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

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f61])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f120,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f121,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f75])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f126,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f64])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f119,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f75])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f130,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f128,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f127])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f58])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f56])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2184,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_47])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_786,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_46])).

cnf(c_2183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2189,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4210,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2183,c_2189])).

cnf(c_4394,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_786,c_4210])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2194,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5911,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4394,c_2194])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3212,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2207])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_360,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_437,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_360])).

cnf(c_2181,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_4754,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3212,c_2181])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2200,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5192,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4754,c_2200])).

cnf(c_6891,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5911,c_5192])).

cnf(c_6892,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6891])).

cnf(c_6901,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2184,c_6892])).

cnf(c_20,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2197,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2211,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5814,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2184,c_2211])).

cnf(c_6132,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_5814])).

cnf(c_6611,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(X0,sK2))) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6132,c_2181])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2199,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7260,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2184,c_2199])).

cnf(c_25797,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(X0,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6611,c_7260])).

cnf(c_25930,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5192,c_25797])).

cnf(c_44,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_158,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_159,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2831,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2200])).

cnf(c_2833,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2831])).

cnf(c_1253,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2673,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_2843,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_1252,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2844,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_11872,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_11873,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11872])).

cnf(c_1258,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_24696,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_24698,plain,
    ( v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24696])).

cnf(c_25968,plain,
    ( ~ v1_relat_1(sK0)
    | k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25930])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2204,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_40,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7668,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_2185])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2596,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_13244,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2596])).

cnf(c_13245,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13244])).

cnf(c_17044,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7668,c_49,c_5192,c_13245])).

cnf(c_17045,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17044])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2186,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7114,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2186])).

cnf(c_2741,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_5491,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_7529,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7114,c_48,c_46,c_5491])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_794,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_43])).

cnf(c_795,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_28,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_28,c_12])).

cnf(c_807,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_795,c_583])).

cnf(c_2171,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_7535,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7529,c_2171])).

cnf(c_13329,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7535,c_49,c_5192,c_13245])).

cnf(c_13330,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13329])).

cnf(c_13336,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_13330])).

cnf(c_17062,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17045,c_13336])).

cnf(c_25,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2192,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_4098,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2180])).

cnf(c_5818,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4098,c_2211])).

cnf(c_6644,plain,
    ( r1_tarski(X0,sK1) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5818,c_5192])).

cnf(c_6645,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_6644])).

cnf(c_6655,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_6645])).

cnf(c_18940,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6655,c_5192])).

cnf(c_37837,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17062,c_18940])).

cnf(c_37839,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_37837])).

cnf(c_38041,plain,
    ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25930,c_44,c_158,c_159,c_2833,c_2843,c_2844,c_5192,c_11873,c_24698,c_25968,c_37839])).

cnf(c_38044,plain,
    ( k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = k7_relat_1(k7_relat_1(sK2,sK0),sK2)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6901,c_38041])).

cnf(c_38138,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_38044,c_5192,c_37839])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_43])).

cnf(c_709,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_2175,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_2457,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2175,c_3])).

cnf(c_7533,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7529,c_2457])).

cnf(c_13471,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7533,c_49,c_5192,c_13245])).

cnf(c_13472,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13471])).

cnf(c_38201,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38138,c_13472])).

cnf(c_33,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_43])).

cnf(c_611,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_625,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_611,c_5])).

cnf(c_2179,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_7534,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7529,c_2179])).

cnf(c_150,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_156,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2672,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_2840,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_2841,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2959,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4379,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9111,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4379])).

cnf(c_1254,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11283,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_11285,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11283])).

cnf(c_13324,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7534,c_45,c_44,c_150,c_156,c_158,c_159,c_2840,c_2841,c_2843,c_2844,c_2959,c_9111,c_11285,c_11873])).

cnf(c_38203,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38138,c_13324])).

cnf(c_38415,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_38203])).

cnf(c_38448,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38201,c_38415])).

cnf(c_38449,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_38448])).

cnf(c_2210,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3497,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2210])).

cnf(c_5194,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5192,c_3497])).

cnf(c_35519,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5194,c_2185])).

cnf(c_35569,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35519,c_3])).

cnf(c_21,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3035,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3038,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3035])).

cnf(c_3040,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_29,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2190,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3633,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2190])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2202,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6000,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_2202])).

cnf(c_6160,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6000,c_5192])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2198,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6169,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6160,c_2198])).

cnf(c_5536,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5537,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5536])).

cnf(c_22408,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6169,c_5192,c_5537])).

cnf(c_22416,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22408,c_2197])).

cnf(c_7822,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7823,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7822])).

cnf(c_34096,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22416,c_5192,c_7823])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2183,c_2187])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8265,c_2188])).

cnf(c_12243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_8714])).

cnf(c_34124,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_34096,c_12243])).

cnf(c_35847,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35569,c_3040,c_5192,c_34124])).

cnf(c_35852,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_35847,c_2207])).

cnf(c_35906,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_35852,c_2210])).

cnf(c_38453,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38449,c_35906])).

cnf(c_2209,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4208,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2209,c_2189])).

cnf(c_2196,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3080,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_2210])).

cnf(c_3314,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3080,c_2831])).

cnf(c_3496,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3314,c_2197])).

cnf(c_3852,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_2831])).

cnf(c_3859,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3852,c_2210])).

cnf(c_4228,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4208,c_3859])).

cnf(c_38454,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38453,c_3,c_4228])).

cnf(c_38455,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_38454])).

cnf(c_155,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38455,c_157])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.68/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.50  
% 7.68/1.50  ------  iProver source info
% 7.68/1.50  
% 7.68/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.50  git: non_committed_changes: false
% 7.68/1.50  git: last_make_outside_of_git: false
% 7.68/1.50  
% 7.68/1.50  ------ 
% 7.68/1.50  
% 7.68/1.50  ------ Input Options
% 7.68/1.50  
% 7.68/1.50  --out_options                           all
% 7.68/1.50  --tptp_safe_out                         true
% 7.68/1.50  --problem_path                          ""
% 7.68/1.50  --include_path                          ""
% 7.68/1.50  --clausifier                            res/vclausify_rel
% 7.68/1.50  --clausifier_options                    --mode clausify
% 7.68/1.50  --stdin                                 false
% 7.68/1.50  --stats_out                             all
% 7.68/1.50  
% 7.68/1.50  ------ General Options
% 7.68/1.50  
% 7.68/1.50  --fof                                   false
% 7.68/1.50  --time_out_real                         305.
% 7.68/1.50  --time_out_virtual                      -1.
% 7.68/1.50  --symbol_type_check                     false
% 7.68/1.50  --clausify_out                          false
% 7.68/1.50  --sig_cnt_out                           false
% 7.68/1.50  --trig_cnt_out                          false
% 7.68/1.50  --trig_cnt_out_tolerance                1.
% 7.68/1.50  --trig_cnt_out_sk_spl                   false
% 7.68/1.50  --abstr_cl_out                          false
% 7.68/1.50  
% 7.68/1.50  ------ Global Options
% 7.68/1.50  
% 7.68/1.50  --schedule                              default
% 7.68/1.50  --add_important_lit                     false
% 7.68/1.50  --prop_solver_per_cl                    1000
% 7.68/1.50  --min_unsat_core                        false
% 7.68/1.50  --soft_assumptions                      false
% 7.68/1.50  --soft_lemma_size                       3
% 7.68/1.50  --prop_impl_unit_size                   0
% 7.68/1.50  --prop_impl_unit                        []
% 7.68/1.50  --share_sel_clauses                     true
% 7.68/1.50  --reset_solvers                         false
% 7.68/1.50  --bc_imp_inh                            [conj_cone]
% 7.68/1.50  --conj_cone_tolerance                   3.
% 7.68/1.50  --extra_neg_conj                        none
% 7.68/1.50  --large_theory_mode                     true
% 7.68/1.50  --prolific_symb_bound                   200
% 7.68/1.50  --lt_threshold                          2000
% 7.68/1.50  --clause_weak_htbl                      true
% 7.68/1.50  --gc_record_bc_elim                     false
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing Options
% 7.68/1.50  
% 7.68/1.50  --preprocessing_flag                    true
% 7.68/1.50  --time_out_prep_mult                    0.1
% 7.68/1.50  --splitting_mode                        input
% 7.68/1.50  --splitting_grd                         true
% 7.68/1.50  --splitting_cvd                         false
% 7.68/1.50  --splitting_cvd_svl                     false
% 7.68/1.50  --splitting_nvd                         32
% 7.68/1.50  --sub_typing                            true
% 7.68/1.50  --prep_gs_sim                           true
% 7.68/1.50  --prep_unflatten                        true
% 7.68/1.50  --prep_res_sim                          true
% 7.68/1.50  --prep_upred                            true
% 7.68/1.50  --prep_sem_filter                       exhaustive
% 7.68/1.50  --prep_sem_filter_out                   false
% 7.68/1.50  --pred_elim                             true
% 7.68/1.50  --res_sim_input                         true
% 7.68/1.50  --eq_ax_congr_red                       true
% 7.68/1.50  --pure_diseq_elim                       true
% 7.68/1.50  --brand_transform                       false
% 7.68/1.50  --non_eq_to_eq                          false
% 7.68/1.50  --prep_def_merge                        true
% 7.68/1.50  --prep_def_merge_prop_impl              false
% 7.68/1.50  --prep_def_merge_mbd                    true
% 7.68/1.50  --prep_def_merge_tr_red                 false
% 7.68/1.50  --prep_def_merge_tr_cl                  false
% 7.68/1.50  --smt_preprocessing                     true
% 7.68/1.50  --smt_ac_axioms                         fast
% 7.68/1.50  --preprocessed_out                      false
% 7.68/1.50  --preprocessed_stats                    false
% 7.68/1.50  
% 7.68/1.50  ------ Abstraction refinement Options
% 7.68/1.50  
% 7.68/1.50  --abstr_ref                             []
% 7.68/1.50  --abstr_ref_prep                        false
% 7.68/1.50  --abstr_ref_until_sat                   false
% 7.68/1.50  --abstr_ref_sig_restrict                funpre
% 7.68/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.50  --abstr_ref_under                       []
% 7.68/1.50  
% 7.68/1.50  ------ SAT Options
% 7.68/1.50  
% 7.68/1.50  --sat_mode                              false
% 7.68/1.50  --sat_fm_restart_options                ""
% 7.68/1.50  --sat_gr_def                            false
% 7.68/1.50  --sat_epr_types                         true
% 7.68/1.50  --sat_non_cyclic_types                  false
% 7.68/1.50  --sat_finite_models                     false
% 7.68/1.50  --sat_fm_lemmas                         false
% 7.68/1.50  --sat_fm_prep                           false
% 7.68/1.50  --sat_fm_uc_incr                        true
% 7.68/1.50  --sat_out_model                         small
% 7.68/1.50  --sat_out_clauses                       false
% 7.68/1.50  
% 7.68/1.50  ------ QBF Options
% 7.68/1.50  
% 7.68/1.50  --qbf_mode                              false
% 7.68/1.50  --qbf_elim_univ                         false
% 7.68/1.50  --qbf_dom_inst                          none
% 7.68/1.50  --qbf_dom_pre_inst                      false
% 7.68/1.50  --qbf_sk_in                             false
% 7.68/1.50  --qbf_pred_elim                         true
% 7.68/1.50  --qbf_split                             512
% 7.68/1.50  
% 7.68/1.50  ------ BMC1 Options
% 7.68/1.50  
% 7.68/1.50  --bmc1_incremental                      false
% 7.68/1.50  --bmc1_axioms                           reachable_all
% 7.68/1.50  --bmc1_min_bound                        0
% 7.68/1.50  --bmc1_max_bound                        -1
% 7.68/1.50  --bmc1_max_bound_default                -1
% 7.68/1.50  --bmc1_symbol_reachability              true
% 7.68/1.50  --bmc1_property_lemmas                  false
% 7.68/1.50  --bmc1_k_induction                      false
% 7.68/1.50  --bmc1_non_equiv_states                 false
% 7.68/1.50  --bmc1_deadlock                         false
% 7.68/1.50  --bmc1_ucm                              false
% 7.68/1.50  --bmc1_add_unsat_core                   none
% 7.68/1.50  --bmc1_unsat_core_children              false
% 7.68/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.50  --bmc1_out_stat                         full
% 7.68/1.50  --bmc1_ground_init                      false
% 7.68/1.50  --bmc1_pre_inst_next_state              false
% 7.68/1.50  --bmc1_pre_inst_state                   false
% 7.68/1.50  --bmc1_pre_inst_reach_state             false
% 7.68/1.50  --bmc1_out_unsat_core                   false
% 7.68/1.50  --bmc1_aig_witness_out                  false
% 7.68/1.50  --bmc1_verbose                          false
% 7.68/1.50  --bmc1_dump_clauses_tptp                false
% 7.68/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.50  --bmc1_dump_file                        -
% 7.68/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.50  --bmc1_ucm_extend_mode                  1
% 7.68/1.50  --bmc1_ucm_init_mode                    2
% 7.68/1.50  --bmc1_ucm_cone_mode                    none
% 7.68/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.50  --bmc1_ucm_relax_model                  4
% 7.68/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.50  --bmc1_ucm_layered_model                none
% 7.68/1.50  --bmc1_ucm_max_lemma_size               10
% 7.68/1.50  
% 7.68/1.50  ------ AIG Options
% 7.68/1.50  
% 7.68/1.50  --aig_mode                              false
% 7.68/1.50  
% 7.68/1.50  ------ Instantiation Options
% 7.68/1.50  
% 7.68/1.50  --instantiation_flag                    true
% 7.68/1.50  --inst_sos_flag                         false
% 7.68/1.50  --inst_sos_phase                        true
% 7.68/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.50  --inst_lit_sel_side                     num_symb
% 7.68/1.50  --inst_solver_per_active                1400
% 7.68/1.50  --inst_solver_calls_frac                1.
% 7.68/1.50  --inst_passive_queue_type               priority_queues
% 7.68/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.50  --inst_passive_queues_freq              [25;2]
% 7.68/1.50  --inst_dismatching                      true
% 7.68/1.50  --inst_eager_unprocessed_to_passive     true
% 7.68/1.50  --inst_prop_sim_given                   true
% 7.68/1.50  --inst_prop_sim_new                     false
% 7.68/1.50  --inst_subs_new                         false
% 7.68/1.50  --inst_eq_res_simp                      false
% 7.68/1.50  --inst_subs_given                       false
% 7.68/1.50  --inst_orphan_elimination               true
% 7.68/1.50  --inst_learning_loop_flag               true
% 7.68/1.50  --inst_learning_start                   3000
% 7.68/1.50  --inst_learning_factor                  2
% 7.68/1.50  --inst_start_prop_sim_after_learn       3
% 7.68/1.50  --inst_sel_renew                        solver
% 7.68/1.50  --inst_lit_activity_flag                true
% 7.68/1.50  --inst_restr_to_given                   false
% 7.68/1.50  --inst_activity_threshold               500
% 7.68/1.50  --inst_out_proof                        true
% 7.68/1.50  
% 7.68/1.50  ------ Resolution Options
% 7.68/1.50  
% 7.68/1.50  --resolution_flag                       true
% 7.68/1.50  --res_lit_sel                           adaptive
% 7.68/1.50  --res_lit_sel_side                      none
% 7.68/1.50  --res_ordering                          kbo
% 7.68/1.50  --res_to_prop_solver                    active
% 7.68/1.50  --res_prop_simpl_new                    false
% 7.68/1.50  --res_prop_simpl_given                  true
% 7.68/1.50  --res_passive_queue_type                priority_queues
% 7.68/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.50  --res_passive_queues_freq               [15;5]
% 7.68/1.50  --res_forward_subs                      full
% 7.68/1.50  --res_backward_subs                     full
% 7.68/1.50  --res_forward_subs_resolution           true
% 7.68/1.50  --res_backward_subs_resolution          true
% 7.68/1.50  --res_orphan_elimination                true
% 7.68/1.50  --res_time_limit                        2.
% 7.68/1.50  --res_out_proof                         true
% 7.68/1.50  
% 7.68/1.50  ------ Superposition Options
% 7.68/1.50  
% 7.68/1.50  --superposition_flag                    true
% 7.68/1.50  --sup_passive_queue_type                priority_queues
% 7.68/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.50  --demod_completeness_check              fast
% 7.68/1.50  --demod_use_ground                      true
% 7.68/1.50  --sup_to_prop_solver                    passive
% 7.68/1.50  --sup_prop_simpl_new                    true
% 7.68/1.50  --sup_prop_simpl_given                  true
% 7.68/1.50  --sup_fun_splitting                     false
% 7.68/1.50  --sup_smt_interval                      50000
% 7.68/1.50  
% 7.68/1.50  ------ Superposition Simplification Setup
% 7.68/1.50  
% 7.68/1.50  --sup_indices_passive                   []
% 7.68/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_full_bw                           [BwDemod]
% 7.68/1.50  --sup_immed_triv                        [TrivRules]
% 7.68/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_immed_bw_main                     []
% 7.68/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.68/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.68/1.50  
% 7.68/1.50  ------ Combination Options
% 7.68/1.50  
% 7.68/1.50  --comb_res_mult                         3
% 7.68/1.50  --comb_sup_mult                         2
% 7.68/1.50  --comb_inst_mult                        10
% 7.68/1.50  
% 7.68/1.50  ------ Debug Options
% 7.68/1.50  
% 7.68/1.50  --dbg_backtrace                         false
% 7.68/1.50  --dbg_dump_prop_clauses                 false
% 7.68/1.50  --dbg_dump_prop_clauses_file            -
% 7.68/1.50  --dbg_out_stat                          false
% 7.68/1.50  ------ Parsing...
% 7.68/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.50  ------ Proving...
% 7.68/1.50  ------ Problem Properties 
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  clauses                                 47
% 7.68/1.50  conjectures                             4
% 7.68/1.50  EPR                                     6
% 7.68/1.50  Horn                                    42
% 7.68/1.50  unary                                   7
% 7.68/1.50  binary                                  13
% 7.68/1.50  lits                                    129
% 7.68/1.50  lits eq                                 37
% 7.68/1.50  fd_pure                                 0
% 7.68/1.50  fd_pseudo                               0
% 7.68/1.50  fd_cond                                 4
% 7.68/1.50  fd_pseudo_cond                          0
% 7.68/1.50  AC symbols                              0
% 7.68/1.50  
% 7.68/1.50  ------ Schedule dynamic 5 is on 
% 7.68/1.50  
% 7.68/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  ------ 
% 7.68/1.50  Current options:
% 7.68/1.50  ------ 
% 7.68/1.50  
% 7.68/1.50  ------ Input Options
% 7.68/1.50  
% 7.68/1.50  --out_options                           all
% 7.68/1.50  --tptp_safe_out                         true
% 7.68/1.50  --problem_path                          ""
% 7.68/1.50  --include_path                          ""
% 7.68/1.50  --clausifier                            res/vclausify_rel
% 7.68/1.50  --clausifier_options                    --mode clausify
% 7.68/1.50  --stdin                                 false
% 7.68/1.50  --stats_out                             all
% 7.68/1.50  
% 7.68/1.50  ------ General Options
% 7.68/1.50  
% 7.68/1.50  --fof                                   false
% 7.68/1.50  --time_out_real                         305.
% 7.68/1.50  --time_out_virtual                      -1.
% 7.68/1.50  --symbol_type_check                     false
% 7.68/1.50  --clausify_out                          false
% 7.68/1.50  --sig_cnt_out                           false
% 7.68/1.50  --trig_cnt_out                          false
% 7.68/1.50  --trig_cnt_out_tolerance                1.
% 7.68/1.50  --trig_cnt_out_sk_spl                   false
% 7.68/1.50  --abstr_cl_out                          false
% 7.68/1.50  
% 7.68/1.50  ------ Global Options
% 7.68/1.50  
% 7.68/1.50  --schedule                              default
% 7.68/1.50  --add_important_lit                     false
% 7.68/1.50  --prop_solver_per_cl                    1000
% 7.68/1.50  --min_unsat_core                        false
% 7.68/1.50  --soft_assumptions                      false
% 7.68/1.50  --soft_lemma_size                       3
% 7.68/1.50  --prop_impl_unit_size                   0
% 7.68/1.50  --prop_impl_unit                        []
% 7.68/1.50  --share_sel_clauses                     true
% 7.68/1.50  --reset_solvers                         false
% 7.68/1.50  --bc_imp_inh                            [conj_cone]
% 7.68/1.50  --conj_cone_tolerance                   3.
% 7.68/1.50  --extra_neg_conj                        none
% 7.68/1.50  --large_theory_mode                     true
% 7.68/1.50  --prolific_symb_bound                   200
% 7.68/1.50  --lt_threshold                          2000
% 7.68/1.50  --clause_weak_htbl                      true
% 7.68/1.50  --gc_record_bc_elim                     false
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing Options
% 7.68/1.50  
% 7.68/1.50  --preprocessing_flag                    true
% 7.68/1.50  --time_out_prep_mult                    0.1
% 7.68/1.50  --splitting_mode                        input
% 7.68/1.50  --splitting_grd                         true
% 7.68/1.50  --splitting_cvd                         false
% 7.68/1.50  --splitting_cvd_svl                     false
% 7.68/1.50  --splitting_nvd                         32
% 7.68/1.50  --sub_typing                            true
% 7.68/1.50  --prep_gs_sim                           true
% 7.68/1.50  --prep_unflatten                        true
% 7.68/1.50  --prep_res_sim                          true
% 7.68/1.50  --prep_upred                            true
% 7.68/1.50  --prep_sem_filter                       exhaustive
% 7.68/1.50  --prep_sem_filter_out                   false
% 7.68/1.50  --pred_elim                             true
% 7.68/1.50  --res_sim_input                         true
% 7.68/1.50  --eq_ax_congr_red                       true
% 7.68/1.50  --pure_diseq_elim                       true
% 7.68/1.50  --brand_transform                       false
% 7.68/1.50  --non_eq_to_eq                          false
% 7.68/1.50  --prep_def_merge                        true
% 7.68/1.50  --prep_def_merge_prop_impl              false
% 7.68/1.50  --prep_def_merge_mbd                    true
% 7.68/1.50  --prep_def_merge_tr_red                 false
% 7.68/1.50  --prep_def_merge_tr_cl                  false
% 7.68/1.50  --smt_preprocessing                     true
% 7.68/1.50  --smt_ac_axioms                         fast
% 7.68/1.50  --preprocessed_out                      false
% 7.68/1.50  --preprocessed_stats                    false
% 7.68/1.50  
% 7.68/1.50  ------ Abstraction refinement Options
% 7.68/1.50  
% 7.68/1.50  --abstr_ref                             []
% 7.68/1.50  --abstr_ref_prep                        false
% 7.68/1.50  --abstr_ref_until_sat                   false
% 7.68/1.50  --abstr_ref_sig_restrict                funpre
% 7.68/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.50  --abstr_ref_under                       []
% 7.68/1.50  
% 7.68/1.50  ------ SAT Options
% 7.68/1.50  
% 7.68/1.50  --sat_mode                              false
% 7.68/1.50  --sat_fm_restart_options                ""
% 7.68/1.50  --sat_gr_def                            false
% 7.68/1.50  --sat_epr_types                         true
% 7.68/1.50  --sat_non_cyclic_types                  false
% 7.68/1.50  --sat_finite_models                     false
% 7.68/1.50  --sat_fm_lemmas                         false
% 7.68/1.50  --sat_fm_prep                           false
% 7.68/1.50  --sat_fm_uc_incr                        true
% 7.68/1.50  --sat_out_model                         small
% 7.68/1.50  --sat_out_clauses                       false
% 7.68/1.50  
% 7.68/1.50  ------ QBF Options
% 7.68/1.50  
% 7.68/1.50  --qbf_mode                              false
% 7.68/1.50  --qbf_elim_univ                         false
% 7.68/1.50  --qbf_dom_inst                          none
% 7.68/1.50  --qbf_dom_pre_inst                      false
% 7.68/1.50  --qbf_sk_in                             false
% 7.68/1.50  --qbf_pred_elim                         true
% 7.68/1.50  --qbf_split                             512
% 7.68/1.50  
% 7.68/1.50  ------ BMC1 Options
% 7.68/1.50  
% 7.68/1.50  --bmc1_incremental                      false
% 7.68/1.50  --bmc1_axioms                           reachable_all
% 7.68/1.50  --bmc1_min_bound                        0
% 7.68/1.50  --bmc1_max_bound                        -1
% 7.68/1.50  --bmc1_max_bound_default                -1
% 7.68/1.50  --bmc1_symbol_reachability              true
% 7.68/1.50  --bmc1_property_lemmas                  false
% 7.68/1.50  --bmc1_k_induction                      false
% 7.68/1.50  --bmc1_non_equiv_states                 false
% 7.68/1.50  --bmc1_deadlock                         false
% 7.68/1.50  --bmc1_ucm                              false
% 7.68/1.50  --bmc1_add_unsat_core                   none
% 7.68/1.50  --bmc1_unsat_core_children              false
% 7.68/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.50  --bmc1_out_stat                         full
% 7.68/1.50  --bmc1_ground_init                      false
% 7.68/1.50  --bmc1_pre_inst_next_state              false
% 7.68/1.50  --bmc1_pre_inst_state                   false
% 7.68/1.50  --bmc1_pre_inst_reach_state             false
% 7.68/1.50  --bmc1_out_unsat_core                   false
% 7.68/1.50  --bmc1_aig_witness_out                  false
% 7.68/1.50  --bmc1_verbose                          false
% 7.68/1.50  --bmc1_dump_clauses_tptp                false
% 7.68/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.50  --bmc1_dump_file                        -
% 7.68/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.50  --bmc1_ucm_extend_mode                  1
% 7.68/1.50  --bmc1_ucm_init_mode                    2
% 7.68/1.50  --bmc1_ucm_cone_mode                    none
% 7.68/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.50  --bmc1_ucm_relax_model                  4
% 7.68/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.50  --bmc1_ucm_layered_model                none
% 7.68/1.50  --bmc1_ucm_max_lemma_size               10
% 7.68/1.50  
% 7.68/1.50  ------ AIG Options
% 7.68/1.50  
% 7.68/1.50  --aig_mode                              false
% 7.68/1.50  
% 7.68/1.50  ------ Instantiation Options
% 7.68/1.50  
% 7.68/1.50  --instantiation_flag                    true
% 7.68/1.50  --inst_sos_flag                         false
% 7.68/1.50  --inst_sos_phase                        true
% 7.68/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.50  --inst_lit_sel_side                     none
% 7.68/1.50  --inst_solver_per_active                1400
% 7.68/1.50  --inst_solver_calls_frac                1.
% 7.68/1.50  --inst_passive_queue_type               priority_queues
% 7.68/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.50  --inst_passive_queues_freq              [25;2]
% 7.68/1.50  --inst_dismatching                      true
% 7.68/1.50  --inst_eager_unprocessed_to_passive     true
% 7.68/1.50  --inst_prop_sim_given                   true
% 7.68/1.50  --inst_prop_sim_new                     false
% 7.68/1.50  --inst_subs_new                         false
% 7.68/1.50  --inst_eq_res_simp                      false
% 7.68/1.50  --inst_subs_given                       false
% 7.68/1.50  --inst_orphan_elimination               true
% 7.68/1.50  --inst_learning_loop_flag               true
% 7.68/1.50  --inst_learning_start                   3000
% 7.68/1.50  --inst_learning_factor                  2
% 7.68/1.50  --inst_start_prop_sim_after_learn       3
% 7.68/1.50  --inst_sel_renew                        solver
% 7.68/1.50  --inst_lit_activity_flag                true
% 7.68/1.50  --inst_restr_to_given                   false
% 7.68/1.50  --inst_activity_threshold               500
% 7.68/1.50  --inst_out_proof                        true
% 7.68/1.50  
% 7.68/1.50  ------ Resolution Options
% 7.68/1.50  
% 7.68/1.50  --resolution_flag                       false
% 7.68/1.50  --res_lit_sel                           adaptive
% 7.68/1.50  --res_lit_sel_side                      none
% 7.68/1.50  --res_ordering                          kbo
% 7.68/1.50  --res_to_prop_solver                    active
% 7.68/1.50  --res_prop_simpl_new                    false
% 7.68/1.50  --res_prop_simpl_given                  true
% 7.68/1.50  --res_passive_queue_type                priority_queues
% 7.68/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.50  --res_passive_queues_freq               [15;5]
% 7.68/1.50  --res_forward_subs                      full
% 7.68/1.50  --res_backward_subs                     full
% 7.68/1.50  --res_forward_subs_resolution           true
% 7.68/1.50  --res_backward_subs_resolution          true
% 7.68/1.50  --res_orphan_elimination                true
% 7.68/1.50  --res_time_limit                        2.
% 7.68/1.50  --res_out_proof                         true
% 7.68/1.50  
% 7.68/1.50  ------ Superposition Options
% 7.68/1.50  
% 7.68/1.50  --superposition_flag                    true
% 7.68/1.50  --sup_passive_queue_type                priority_queues
% 7.68/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.50  --demod_completeness_check              fast
% 7.68/1.50  --demod_use_ground                      true
% 7.68/1.50  --sup_to_prop_solver                    passive
% 7.68/1.50  --sup_prop_simpl_new                    true
% 7.68/1.50  --sup_prop_simpl_given                  true
% 7.68/1.50  --sup_fun_splitting                     false
% 7.68/1.50  --sup_smt_interval                      50000
% 7.68/1.50  
% 7.68/1.50  ------ Superposition Simplification Setup
% 7.68/1.50  
% 7.68/1.50  --sup_indices_passive                   []
% 7.68/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_full_bw                           [BwDemod]
% 7.68/1.50  --sup_immed_triv                        [TrivRules]
% 7.68/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_immed_bw_main                     []
% 7.68/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.68/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.68/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.68/1.50  
% 7.68/1.50  ------ Combination Options
% 7.68/1.50  
% 7.68/1.50  --comb_res_mult                         3
% 7.68/1.50  --comb_sup_mult                         2
% 7.68/1.50  --comb_inst_mult                        10
% 7.68/1.50  
% 7.68/1.50  ------ Debug Options
% 7.68/1.50  
% 7.68/1.50  --dbg_backtrace                         false
% 7.68/1.50  --dbg_dump_prop_clauses                 false
% 7.68/1.50  --dbg_dump_prop_clauses_file            -
% 7.68/1.50  --dbg_out_stat                          false
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  ------ Proving...
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  % SZS status Theorem for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  fof(f29,conjecture,(
% 7.68/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f30,negated_conjecture,(
% 7.68/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.68/1.50    inference(negated_conjecture,[],[f29])).
% 7.68/1.50  
% 7.68/1.50  fof(f66,plain,(
% 7.68/1.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.68/1.50    inference(ennf_transformation,[],[f30])).
% 7.68/1.50  
% 7.68/1.50  fof(f67,plain,(
% 7.68/1.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.68/1.50    inference(flattening,[],[f66])).
% 7.68/1.50  
% 7.68/1.50  fof(f74,plain,(
% 7.68/1.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.68/1.50    introduced(choice_axiom,[])).
% 7.68/1.50  
% 7.68/1.50  fof(f75,plain,(
% 7.68/1.50    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.68/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f74])).
% 7.68/1.50  
% 7.68/1.50  fof(f122,plain,(
% 7.68/1.50    r1_tarski(sK2,sK0)),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f26,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f60,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(ennf_transformation,[],[f26])).
% 7.68/1.50  
% 7.68/1.50  fof(f61,plain,(
% 7.68/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(flattening,[],[f60])).
% 7.68/1.50  
% 7.68/1.50  fof(f73,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(nnf_transformation,[],[f61])).
% 7.68/1.50  
% 7.68/1.50  fof(f109,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f73])).
% 7.68/1.50  
% 7.68/1.50  fof(f120,plain,(
% 7.68/1.50    v1_funct_2(sK3,sK0,sK1)),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f121,plain,(
% 7.68/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f23,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f55,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(ennf_transformation,[],[f23])).
% 7.68/1.50  
% 7.68/1.50  fof(f106,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f55])).
% 7.68/1.50  
% 7.68/1.50  fof(f18,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f48,plain,(
% 7.68/1.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(ennf_transformation,[],[f18])).
% 7.68/1.50  
% 7.68/1.50  fof(f49,plain,(
% 7.68/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(flattening,[],[f48])).
% 7.68/1.50  
% 7.68/1.50  fof(f99,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f49])).
% 7.68/1.50  
% 7.68/1.50  fof(f5,axiom,(
% 7.68/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f70,plain,(
% 7.68/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.68/1.50    inference(nnf_transformation,[],[f5])).
% 7.68/1.50  
% 7.68/1.50  fof(f82,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f70])).
% 7.68/1.50  
% 7.68/1.50  fof(f7,axiom,(
% 7.68/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f35,plain,(
% 7.68/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f7])).
% 7.68/1.50  
% 7.68/1.50  fof(f84,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f35])).
% 7.68/1.50  
% 7.68/1.50  fof(f83,plain,(
% 7.68/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f70])).
% 7.68/1.50  
% 7.68/1.50  fof(f12,axiom,(
% 7.68/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f93,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f12])).
% 7.68/1.50  
% 7.68/1.50  fof(f15,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f45,plain,(
% 7.68/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(ennf_transformation,[],[f15])).
% 7.68/1.50  
% 7.68/1.50  fof(f96,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f45])).
% 7.68/1.50  
% 7.68/1.50  fof(f1,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f32,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.68/1.50    inference(ennf_transformation,[],[f1])).
% 7.68/1.50  
% 7.68/1.50  fof(f33,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.68/1.50    inference(flattening,[],[f32])).
% 7.68/1.50  
% 7.68/1.50  fof(f76,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f33])).
% 7.68/1.50  
% 7.68/1.50  fof(f13,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f41,plain,(
% 7.68/1.50    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.68/1.50    inference(ennf_transformation,[],[f13])).
% 7.68/1.50  
% 7.68/1.50  fof(f42,plain,(
% 7.68/1.50    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.68/1.50    inference(flattening,[],[f41])).
% 7.68/1.50  
% 7.68/1.50  fof(f94,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f42])).
% 7.68/1.50  
% 7.68/1.50  fof(f123,plain,(
% 7.68/1.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f3,axiom,(
% 7.68/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f68,plain,(
% 7.68/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.68/1.50    inference(nnf_transformation,[],[f3])).
% 7.68/1.50  
% 7.68/1.50  fof(f69,plain,(
% 7.68/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.68/1.50    inference(flattening,[],[f68])).
% 7.68/1.50  
% 7.68/1.50  fof(f78,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f69])).
% 7.68/1.50  
% 7.68/1.50  fof(f79,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.68/1.50    inference(cnf_transformation,[],[f69])).
% 7.68/1.50  
% 7.68/1.50  fof(f126,plain,(
% 7.68/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.68/1.50    inference(equality_resolution,[],[f79])).
% 7.68/1.50  
% 7.68/1.50  fof(f80,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.68/1.50    inference(cnf_transformation,[],[f69])).
% 7.68/1.50  
% 7.68/1.50  fof(f125,plain,(
% 7.68/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.68/1.50    inference(equality_resolution,[],[f80])).
% 7.68/1.50  
% 7.68/1.50  fof(f10,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f38,plain,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.68/1.50    inference(ennf_transformation,[],[f10])).
% 7.68/1.50  
% 7.68/1.50  fof(f89,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f38])).
% 7.68/1.50  
% 7.68/1.50  fof(f28,axiom,(
% 7.68/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f64,plain,(
% 7.68/1.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.68/1.50    inference(ennf_transformation,[],[f28])).
% 7.68/1.50  
% 7.68/1.50  fof(f65,plain,(
% 7.68/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(flattening,[],[f64])).
% 7.68/1.50  
% 7.68/1.50  fof(f118,plain,(
% 7.68/1.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f65])).
% 7.68/1.50  
% 7.68/1.50  fof(f119,plain,(
% 7.68/1.50    v1_funct_1(sK3)),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f21,axiom,(
% 7.68/1.50    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f52,plain,(
% 7.68/1.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.68/1.50    inference(ennf_transformation,[],[f21])).
% 7.68/1.50  
% 7.68/1.50  fof(f53,plain,(
% 7.68/1.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.68/1.50    inference(flattening,[],[f52])).
% 7.68/1.50  
% 7.68/1.50  fof(f103,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f53])).
% 7.68/1.50  
% 7.68/1.50  fof(f27,axiom,(
% 7.68/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f62,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.68/1.50    inference(ennf_transformation,[],[f27])).
% 7.68/1.50  
% 7.68/1.50  fof(f63,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.68/1.50    inference(flattening,[],[f62])).
% 7.68/1.50  
% 7.68/1.50  fof(f115,plain,(
% 7.68/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f63])).
% 7.68/1.50  
% 7.68/1.50  fof(f117,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f65])).
% 7.68/1.50  
% 7.68/1.50  fof(f124,plain,(
% 7.68/1.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.68/1.50    inference(cnf_transformation,[],[f75])).
% 7.68/1.50  
% 7.68/1.50  fof(f22,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f54,plain,(
% 7.68/1.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.68/1.50    inference(ennf_transformation,[],[f22])).
% 7.68/1.50  
% 7.68/1.50  fof(f105,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f54])).
% 7.68/1.50  
% 7.68/1.50  fof(f9,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f37,plain,(
% 7.68/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(ennf_transformation,[],[f9])).
% 7.68/1.50  
% 7.68/1.50  fof(f72,plain,(
% 7.68/1.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(nnf_transformation,[],[f37])).
% 7.68/1.50  
% 7.68/1.50  fof(f87,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f72])).
% 7.68/1.50  
% 7.68/1.50  fof(f20,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f51,plain,(
% 7.68/1.50    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(ennf_transformation,[],[f20])).
% 7.68/1.50  
% 7.68/1.50  fof(f101,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f51])).
% 7.68/1.50  
% 7.68/1.50  fof(f112,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f73])).
% 7.68/1.50  
% 7.68/1.50  fof(f130,plain,(
% 7.68/1.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.68/1.50    inference(equality_resolution,[],[f112])).
% 7.68/1.50  
% 7.68/1.50  fof(f114,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f73])).
% 7.68/1.50  
% 7.68/1.50  fof(f127,plain,(
% 7.68/1.50    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(equality_resolution,[],[f114])).
% 7.68/1.50  
% 7.68/1.50  fof(f128,plain,(
% 7.68/1.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.68/1.50    inference(equality_resolution,[],[f127])).
% 7.68/1.50  
% 7.68/1.50  fof(f4,axiom,(
% 7.68/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f81,plain,(
% 7.68/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f4])).
% 7.68/1.50  
% 7.68/1.50  fof(f2,axiom,(
% 7.68/1.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f34,plain,(
% 7.68/1.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.68/1.50    inference(ennf_transformation,[],[f2])).
% 7.68/1.50  
% 7.68/1.50  fof(f77,plain,(
% 7.68/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f34])).
% 7.68/1.50  
% 7.68/1.50  fof(f16,axiom,(
% 7.68/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f46,plain,(
% 7.68/1.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(ennf_transformation,[],[f16])).
% 7.68/1.50  
% 7.68/1.50  fof(f97,plain,(
% 7.68/1.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f46])).
% 7.68/1.50  
% 7.68/1.50  fof(f104,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f54])).
% 7.68/1.50  
% 7.68/1.50  fof(f11,axiom,(
% 7.68/1.50    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f39,plain,(
% 7.68/1.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 7.68/1.50    inference(ennf_transformation,[],[f11])).
% 7.68/1.50  
% 7.68/1.50  fof(f40,plain,(
% 7.68/1.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 7.68/1.50    inference(flattening,[],[f39])).
% 7.68/1.50  
% 7.68/1.50  fof(f91,plain,(
% 7.68/1.50    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f40])).
% 7.68/1.50  
% 7.68/1.50  fof(f14,axiom,(
% 7.68/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f43,plain,(
% 7.68/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.68/1.50    inference(ennf_transformation,[],[f14])).
% 7.68/1.50  
% 7.68/1.50  fof(f44,plain,(
% 7.68/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.68/1.50    inference(flattening,[],[f43])).
% 7.68/1.50  
% 7.68/1.50  fof(f95,plain,(
% 7.68/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.68/1.50    inference(cnf_transformation,[],[f44])).
% 7.68/1.50  
% 7.68/1.50  fof(f25,axiom,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f58,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.68/1.50    inference(ennf_transformation,[],[f25])).
% 7.68/1.50  
% 7.68/1.50  fof(f59,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.68/1.50    inference(flattening,[],[f58])).
% 7.68/1.50  
% 7.68/1.50  fof(f108,plain,(
% 7.68/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f59])).
% 7.68/1.50  
% 7.68/1.50  fof(f24,axiom,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.68/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.50  
% 7.68/1.50  fof(f56,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.68/1.50    inference(ennf_transformation,[],[f24])).
% 7.68/1.50  
% 7.68/1.50  fof(f57,plain,(
% 7.68/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.68/1.50    inference(flattening,[],[f56])).
% 7.68/1.50  
% 7.68/1.50  fof(f107,plain,(
% 7.68/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.68/1.50    inference(cnf_transformation,[],[f57])).
% 7.68/1.50  
% 7.68/1.50  cnf(c_45,negated_conjecture,
% 7.68/1.50      ( r1_tarski(sK2,sK0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2184,plain,
% 7.68/1.50      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38,plain,
% 7.68/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.68/1.50      | k1_xboole_0 = X2 ),
% 7.68/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_47,negated_conjecture,
% 7.68/1.50      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_783,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.68/1.50      | sK3 != X0
% 7.68/1.50      | sK1 != X2
% 7.68/1.50      | sK0 != X1
% 7.68/1.50      | k1_xboole_0 = X2 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_38,c_47]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_784,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.68/1.50      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.68/1.50      | k1_xboole_0 = sK1 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_783]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_46,negated_conjecture,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.68/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_786,plain,
% 7.68/1.50      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_784,c_46]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2183,plain,
% 7.68/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_30,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2189,plain,
% 7.68/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.68/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4210,plain,
% 7.68/1.50      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2189]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4394,plain,
% 7.68/1.50      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_786,c_4210]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_23,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.68/1.50      | ~ v1_relat_1(X1)
% 7.68/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2194,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.68/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5911,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.68/1.50      | sK1 = k1_xboole_0
% 7.68/1.50      | r1_tarski(X0,sK0) != iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_4394,c_2194]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2207,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.68/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3212,plain,
% 7.68/1.50      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2207]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_8,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.68/1.50      | ~ v1_relat_1(X1)
% 7.68/1.50      | v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_359,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.68/1.50      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_360,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_359]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_437,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.68/1.50      inference(bin_hyper_res,[status(thm)],[c_8,c_360]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2181,plain,
% 7.68/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.50      | v1_relat_1(X1) != iProver_top
% 7.68/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4754,plain,
% 7.68/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.68/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_3212,c_2181]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_17,plain,
% 7.68/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2200,plain,
% 7.68/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5192,plain,
% 7.68/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_4754,c_2200]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6891,plain,
% 7.68/1.50      ( r1_tarski(X0,sK0) != iProver_top
% 7.68/1.50      | sK1 = k1_xboole_0
% 7.68/1.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_5911,c_5192]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6892,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.68/1.50      | sK1 = k1_xboole_0
% 7.68/1.50      | r1_tarski(X0,sK0) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_6891]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6901,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2184,c_6892]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_20,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2197,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_0,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.68/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2211,plain,
% 7.68/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.68/1.50      | r1_tarski(X2,X0) != iProver_top
% 7.68/1.50      | r1_tarski(X2,X1) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5814,plain,
% 7.68/1.50      ( r1_tarski(X0,sK2) != iProver_top
% 7.68/1.50      | r1_tarski(X0,sK0) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2184,c_2211]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6132,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK0) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2197,c_5814]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6611,plain,
% 7.68/1.50      ( v1_relat_1(X0) != iProver_top
% 7.68/1.50      | v1_relat_1(k1_relat_1(k7_relat_1(X0,sK2))) = iProver_top
% 7.68/1.50      | v1_relat_1(sK0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6132,c_2181]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_18,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1)
% 7.68/1.50      | ~ v1_relat_1(X2)
% 7.68/1.50      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2199,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
% 7.68/1.50      | r1_tarski(X2,X1) != iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7260,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK2)
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2184,c_2199]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25797,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(X0,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
% 7.68/1.50      | v1_relat_1(X0) != iProver_top
% 7.68/1.50      | v1_relat_1(sK0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6611,c_7260]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25930,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 7.68/1.50      | v1_relat_1(sK0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_5192,c_25797]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_44,negated_conjecture,
% 7.68/1.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4,plain,
% 7.68/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = X0
% 7.68/1.50      | k1_xboole_0 = X1 ),
% 7.68/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_158,plain,
% 7.68/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3,plain,
% 7.68/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_159,plain,
% 7.68/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2,plain,
% 7.68/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2831,plain,
% 7.68/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2,c_2200]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2833,plain,
% 7.68/1.50      ( v1_relat_1(k1_xboole_0) ),
% 7.68/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2831]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1253,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2673,plain,
% 7.68/1.50      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1253]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2843,plain,
% 7.68/1.50      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_2673]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1252,plain,( X0 = X0 ),theory(equality) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2844,plain,
% 7.68/1.50      ( sK0 = sK0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_11872,plain,
% 7.68/1.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1253]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_11873,plain,
% 7.68/1.50      ( sK1 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = sK1
% 7.68/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_11872]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1258,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.68/1.50      theory(equality) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_24696,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(sK0) | sK0 != X0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1258]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_24698,plain,
% 7.68/1.50      ( v1_relat_1(sK0)
% 7.68/1.50      | ~ v1_relat_1(k1_xboole_0)
% 7.68/1.50      | sK0 != k1_xboole_0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_24696]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25968,plain,
% 7.68/1.50      ( ~ v1_relat_1(sK0)
% 7.68/1.50      | k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
% 7.68/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_25930]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13,plain,
% 7.68/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2204,plain,
% 7.68/1.50      ( v1_relat_1(X0) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_40,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.68/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2185,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.68/1.50      | v1_funct_1(X0) != iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7668,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6901,c_2185]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_48,negated_conjecture,
% 7.68/1.50      ( v1_funct_1(sK3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_49,plain,
% 7.68/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_26,plain,
% 7.68/1.50      ( ~ v1_funct_1(X0)
% 7.68/1.50      | v1_funct_1(k7_relat_1(X0,X1))
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2596,plain,
% 7.68/1.50      ( v1_funct_1(k7_relat_1(sK3,X0))
% 7.68/1.50      | ~ v1_funct_1(sK3)
% 7.68/1.50      | ~ v1_relat_1(sK3) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13244,plain,
% 7.68/1.50      ( v1_funct_1(k7_relat_1(sK3,sK2))
% 7.68/1.50      | ~ v1_funct_1(sK3)
% 7.68/1.50      | ~ v1_relat_1(sK3) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_2596]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13245,plain,
% 7.68/1.50      ( v1_funct_1(k7_relat_1(sK3,sK2)) = iProver_top
% 7.68/1.50      | v1_funct_1(sK3) != iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_13244]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_17044,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.68/1.50      | sK1 = k1_xboole_0
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_7668,c_49,c_5192,c_13245]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_17045,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_17044]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_39,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2186,plain,
% 7.68/1.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.68/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.68/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7114,plain,
% 7.68/1.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.68/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2186]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2741,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.68/1.50      | ~ v1_funct_1(sK3)
% 7.68/1.50      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5491,plain,
% 7.68/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.68/1.50      | ~ v1_funct_1(sK3)
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_2741]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7529,plain,
% 7.68/1.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_7114,c_48,c_46,c_5491]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_41,plain,
% 7.68/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.68/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_43,negated_conjecture,
% 7.68/1.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.68/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_794,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.68/1.50      | ~ v1_funct_1(X0)
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | ~ v1_relat_1(X0)
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.68/1.50      | k1_relat_1(X0) != sK2
% 7.68/1.50      | sK1 != X1 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_41,c_43]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_795,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_794]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_28,plain,
% 7.68/1.50      ( v5_relat_1(X0,X1)
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.68/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_12,plain,
% 7.68/1.50      ( ~ v5_relat_1(X0,X1)
% 7.68/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_583,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | r1_tarski(k2_relat_1(X0),X2)
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(resolution,[status(thm)],[c_28,c_12]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_807,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_795,c_583]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2171,plain,
% 7.68/1.50      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 7.68/1.50      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7535,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_7529,c_2171]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13329,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_7535,c_49,c_5192,c_13245]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13330,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_13329]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13336,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6901,c_13330]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_17062,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0
% 7.68/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_17045,c_13336]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_25,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2192,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2180,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4098,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2180]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5818,plain,
% 7.68/1.50      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 7.68/1.50      | r1_tarski(X0,sK1) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_4098,c_2211]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6644,plain,
% 7.68/1.50      ( r1_tarski(X0,sK1) = iProver_top
% 7.68/1.50      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_5818,c_5192]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6645,plain,
% 7.68/1.50      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 7.68/1.50      | r1_tarski(X0,sK1) = iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_6644]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6655,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2192,c_6645]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_18940,plain,
% 7.68/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_6655,c_5192]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_37837,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(forward_subsumption_resolution,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_17062,c_18940]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_37839,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2204,c_37837]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38041,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK0),sK2) = k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_25930,c_44,c_158,c_159,c_2833,c_2843,c_2844,c_5192,
% 7.68/1.50                 c_11873,c_24698,c_25968,c_37839]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38044,plain,
% 7.68/1.50      ( k7_relat_1(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = k7_relat_1(k7_relat_1(sK2,sK0),sK2)
% 7.68/1.50      | sK1 = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6901,c_38041]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38138,plain,
% 7.68/1.50      ( sK1 = k1_xboole_0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_38044,c_5192,c_37839]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35,plain,
% 7.68/1.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.68/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_708,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.68/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.68/1.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | sK1 != X1 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_35,c_43]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_709,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_708]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2175,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2457,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.68/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_2175,c_3]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7533,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_7529,c_2457]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13471,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_7533,c_49,c_5192,c_13245]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13472,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(renaming,[status(thm)],[c_13471]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38201,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 7.68/1.50      | sK2 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_38138,c_13472]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_33,plain,
% 7.68/1.50      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.68/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.68/1.50      | k1_xboole_0 = X0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f128]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_610,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.68/1.50      | sK2 != X0
% 7.68/1.50      | sK1 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = X0 ),
% 7.68/1.50      inference(resolution_lifted,[status(thm)],[c_33,c_43]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_611,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.68/1.50      | sK1 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = sK2 ),
% 7.68/1.50      inference(unflattening,[status(thm)],[c_610]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.68/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_625,plain,
% 7.68/1.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.68/1.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.68/1.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.68/1.50      | sK1 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = sK2 ),
% 7.68/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_611,c_5]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2179,plain,
% 7.68/1.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.68/1.50      | sK1 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 = sK2
% 7.68/1.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7534,plain,
% 7.68/1.50      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.68/1.50      | sK2 = k1_xboole_0
% 7.68/1.50      | sK1 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_7529,c_2179]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_150,plain,
% 7.68/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.68/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_156,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2672,plain,
% 7.68/1.50      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1253]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2840,plain,
% 7.68/1.50      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_2672]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2841,plain,
% 7.68/1.50      ( sK2 = sK2 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2959,plain,
% 7.68/1.50      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4379,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,k1_xboole_0)
% 7.68/1.50      | ~ r1_tarski(sK2,X0)
% 7.68/1.50      | r1_tarski(sK2,k1_xboole_0) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_9111,plain,
% 7.68/1.50      ( ~ r1_tarski(sK2,sK0)
% 7.68/1.50      | r1_tarski(sK2,k1_xboole_0)
% 7.68/1.50      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_4379]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_1254,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.50      theory(equality) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_11283,plain,
% 7.68/1.50      ( ~ r1_tarski(X0,X1)
% 7.68/1.50      | r1_tarski(sK0,k1_xboole_0)
% 7.68/1.50      | sK0 != X0
% 7.68/1.50      | k1_xboole_0 != X1 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_1254]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_11285,plain,
% 7.68/1.50      ( r1_tarski(sK0,k1_xboole_0)
% 7.68/1.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.68/1.50      | sK0 != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_11283]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_13324,plain,
% 7.68/1.50      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_7534,c_45,c_44,c_150,c_156,c_158,c_159,c_2840,c_2841,
% 7.68/1.50                 c_2843,c_2844,c_2959,c_9111,c_11285,c_11873]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38203,plain,
% 7.68/1.50      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_38138,c_13324]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38415,plain,
% 7.68/1.50      ( sK2 = k1_xboole_0 ),
% 7.68/1.50      inference(equality_resolution_simp,[status(thm)],[c_38203]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38448,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.68/1.50      | k1_xboole_0 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_38201,c_38415]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38449,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.68/1.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(equality_resolution_simp,[status(thm)],[c_38448]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2210,plain,
% 7.68/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3497,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2197,c_2210]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5194,plain,
% 7.68/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_5192,c_3497]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35519,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_5194,c_2185]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35569,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.68/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 7.68/1.50      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_35519,c_3]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_21,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3035,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3038,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_3035]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3040,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_3038]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_29,plain,
% 7.68/1.50      ( v4_relat_1(X0,X1)
% 7.68/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.68/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2190,plain,
% 7.68/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.68/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3633,plain,
% 7.68/1.50      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2190]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_15,plain,
% 7.68/1.50      ( ~ v4_relat_1(X0,X1)
% 7.68/1.50      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 7.68/1.50      | ~ v1_relat_1(X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2202,plain,
% 7.68/1.50      ( v4_relat_1(X0,X1) != iProver_top
% 7.68/1.50      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6000,plain,
% 7.68/1.50      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_3633,c_2202]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6160,plain,
% 7.68/1.50      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_6000,c_5192]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_19,plain,
% 7.68/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.68/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2198,plain,
% 7.68/1.50      ( k7_relat_1(X0,X1) = X0
% 7.68/1.50      | v4_relat_1(X0,X1) != iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_6169,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_6160,c_2198]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5536,plain,
% 7.68/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_5537,plain,
% 7.68/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_5536]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_22408,plain,
% 7.68/1.50      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_6169,c_5192,c_5537]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_22416,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 7.68/1.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_22408,c_2197]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7822,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 7.68/1.50      | ~ v1_relat_1(sK3) ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_7823,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 7.68/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_7822]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_34096,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_22416,c_5192,c_7823]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_32,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | ~ r1_tarski(X3,X0) ),
% 7.68/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2187,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.68/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.68/1.50      | r1_tarski(X3,X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_8265,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.68/1.50      | r1_tarski(X0,sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2183,c_2187]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_31,plain,
% 7.68/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.68/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.68/1.50      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.68/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2188,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.68/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.68/1.50      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_8714,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.68/1.50      | r1_tarski(X0,sK3) != iProver_top
% 7.68/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_8265,c_2188]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_12243,plain,
% 7.68/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.68/1.50      | r1_tarski(X0,sK3) != iProver_top
% 7.68/1.50      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_3,c_8714]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_34124,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.68/1.50      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_34096,c_12243]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35847,plain,
% 7.68/1.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_35569,c_3040,c_5192,c_34124]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35852,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_35847,c_2207]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_35906,plain,
% 7.68/1.50      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_35852,c_2210]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38453,plain,
% 7.68/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.68/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_38449,c_35906]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2209,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4208,plain,
% 7.68/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2209,c_2189]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_2196,plain,
% 7.68/1.50      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 7.68/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3080,plain,
% 7.68/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 7.68/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_2196,c_2210]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3314,plain,
% 7.68/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_3080,c_2831]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3496,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 7.68/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_3314,c_2197]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3852,plain,
% 7.68/1.50      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.68/1.50      inference(global_propositional_subsumption,
% 7.68/1.50                [status(thm)],
% 7.68/1.50                [c_3496,c_2831]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_3859,plain,
% 7.68/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(superposition,[status(thm)],[c_3852,c_2210]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_4228,plain,
% 7.68/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.50      inference(light_normalisation,[status(thm)],[c_4208,c_3859]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38454,plain,
% 7.68/1.50      ( k1_xboole_0 != k1_xboole_0
% 7.68/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(demodulation,[status(thm)],[c_38453,c_3,c_4228]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_38455,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.68/1.50      inference(equality_resolution_simp,[status(thm)],[c_38454]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_155,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.68/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(c_157,plain,
% 7.68/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.68/1.50      inference(instantiation,[status(thm)],[c_155]) ).
% 7.68/1.50  
% 7.68/1.50  cnf(contradiction,plain,
% 7.68/1.50      ( $false ),
% 7.68/1.50      inference(minisat,[status(thm)],[c_38455,c_157]) ).
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.50  
% 7.68/1.50  ------                               Statistics
% 7.68/1.50  
% 7.68/1.50  ------ General
% 7.68/1.50  
% 7.68/1.50  abstr_ref_over_cycles:                  0
% 7.68/1.50  abstr_ref_under_cycles:                 0
% 7.68/1.50  gc_basic_clause_elim:                   0
% 7.68/1.50  forced_gc_time:                         0
% 7.68/1.50  parsing_time:                           0.01
% 7.68/1.50  unif_index_cands_time:                  0.
% 7.68/1.50  unif_index_add_time:                    0.
% 7.68/1.50  orderings_time:                         0.
% 7.68/1.50  out_proof_time:                         0.023
% 7.68/1.50  total_time:                             0.895
% 7.68/1.50  num_of_symbols:                         50
% 7.68/1.50  num_of_terms:                           25221
% 7.68/1.50  
% 7.68/1.50  ------ Preprocessing
% 7.68/1.50  
% 7.68/1.50  num_of_splits:                          0
% 7.68/1.50  num_of_split_atoms:                     0
% 7.68/1.50  num_of_reused_defs:                     0
% 7.68/1.50  num_eq_ax_congr_red:                    7
% 7.68/1.50  num_of_sem_filtered_clauses:            1
% 7.68/1.50  num_of_subtypes:                        0
% 7.68/1.50  monotx_restored_types:                  0
% 7.68/1.50  sat_num_of_epr_types:                   0
% 7.68/1.50  sat_num_of_non_cyclic_types:            0
% 7.68/1.50  sat_guarded_non_collapsed_types:        0
% 7.68/1.50  num_pure_diseq_elim:                    0
% 7.68/1.50  simp_replaced_by:                       0
% 7.68/1.50  res_preprocessed:                       217
% 7.68/1.50  prep_upred:                             0
% 7.68/1.50  prep_unflattend:                        43
% 7.68/1.50  smt_new_axioms:                         0
% 7.68/1.50  pred_elim_cands:                        5
% 7.68/1.50  pred_elim:                              2
% 7.68/1.50  pred_elim_cl:                           0
% 7.68/1.50  pred_elim_cycles:                       4
% 7.68/1.50  merged_defs:                            8
% 7.68/1.50  merged_defs_ncl:                        0
% 7.68/1.50  bin_hyper_res:                          9
% 7.68/1.50  prep_cycles:                            4
% 7.68/1.50  pred_elim_time:                         0.009
% 7.68/1.50  splitting_time:                         0.
% 7.68/1.50  sem_filter_time:                        0.
% 7.68/1.50  monotx_time:                            0.001
% 7.68/1.50  subtype_inf_time:                       0.
% 7.68/1.50  
% 7.68/1.50  ------ Problem properties
% 7.68/1.50  
% 7.68/1.50  clauses:                                47
% 7.68/1.50  conjectures:                            4
% 7.68/1.50  epr:                                    6
% 7.68/1.50  horn:                                   42
% 7.68/1.50  ground:                                 12
% 7.68/1.50  unary:                                  7
% 7.68/1.50  binary:                                 13
% 7.68/1.50  lits:                                   129
% 7.68/1.50  lits_eq:                                37
% 7.68/1.50  fd_pure:                                0
% 7.68/1.50  fd_pseudo:                              0
% 7.68/1.50  fd_cond:                                4
% 7.68/1.50  fd_pseudo_cond:                         0
% 7.68/1.50  ac_symbols:                             0
% 7.68/1.50  
% 7.68/1.50  ------ Propositional Solver
% 7.68/1.50  
% 7.68/1.50  prop_solver_calls:                      30
% 7.68/1.50  prop_fast_solver_calls:                 2174
% 7.68/1.50  smt_solver_calls:                       0
% 7.68/1.50  smt_fast_solver_calls:                  0
% 7.68/1.50  prop_num_of_clauses:                    12647
% 7.68/1.50  prop_preprocess_simplified:             22151
% 7.68/1.50  prop_fo_subsumed:                       84
% 7.68/1.50  prop_solver_time:                       0.
% 7.68/1.50  smt_solver_time:                        0.
% 7.68/1.50  smt_fast_solver_time:                   0.
% 7.68/1.50  prop_fast_solver_time:                  0.
% 7.68/1.50  prop_unsat_core_time:                   0.001
% 7.68/1.50  
% 7.68/1.50  ------ QBF
% 7.68/1.50  
% 7.68/1.50  qbf_q_res:                              0
% 7.68/1.50  qbf_num_tautologies:                    0
% 7.68/1.50  qbf_prep_cycles:                        0
% 7.68/1.50  
% 7.68/1.50  ------ BMC1
% 7.68/1.50  
% 7.68/1.50  bmc1_current_bound:                     -1
% 7.68/1.50  bmc1_last_solved_bound:                 -1
% 7.68/1.50  bmc1_unsat_core_size:                   -1
% 7.68/1.50  bmc1_unsat_core_parents_size:           -1
% 7.68/1.50  bmc1_merge_next_fun:                    0
% 7.68/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.68/1.50  
% 7.68/1.50  ------ Instantiation
% 7.68/1.50  
% 7.68/1.50  inst_num_of_clauses:                    3137
% 7.68/1.50  inst_num_in_passive:                    630
% 7.68/1.50  inst_num_in_active:                     1430
% 7.68/1.50  inst_num_in_unprocessed:                1079
% 7.68/1.50  inst_num_of_loops:                      1570
% 7.68/1.50  inst_num_of_learning_restarts:          0
% 7.68/1.50  inst_num_moves_active_passive:          136
% 7.68/1.50  inst_lit_activity:                      0
% 7.68/1.50  inst_lit_activity_moves:                0
% 7.68/1.50  inst_num_tautologies:                   0
% 7.68/1.50  inst_num_prop_implied:                  0
% 7.68/1.50  inst_num_existing_simplified:           0
% 7.68/1.50  inst_num_eq_res_simplified:             0
% 7.68/1.50  inst_num_child_elim:                    0
% 7.68/1.50  inst_num_of_dismatching_blockings:      2624
% 7.68/1.50  inst_num_of_non_proper_insts:           4791
% 7.68/1.50  inst_num_of_duplicates:                 0
% 7.68/1.50  inst_inst_num_from_inst_to_res:         0
% 7.68/1.50  inst_dismatching_checking_time:         0.
% 7.68/1.50  
% 7.68/1.50  ------ Resolution
% 7.68/1.50  
% 7.68/1.50  res_num_of_clauses:                     0
% 7.68/1.50  res_num_in_passive:                     0
% 7.68/1.50  res_num_in_active:                      0
% 7.68/1.50  res_num_of_loops:                       221
% 7.68/1.50  res_forward_subset_subsumed:            89
% 7.68/1.50  res_backward_subset_subsumed:           8
% 7.68/1.50  res_forward_subsumed:                   0
% 7.68/1.50  res_backward_subsumed:                  0
% 7.68/1.50  res_forward_subsumption_resolution:     4
% 7.68/1.50  res_backward_subsumption_resolution:    0
% 7.68/1.50  res_clause_to_clause_subsumption:       3541
% 7.68/1.50  res_orphan_elimination:                 0
% 7.68/1.50  res_tautology_del:                      289
% 7.68/1.50  res_num_eq_res_simplified:              1
% 7.68/1.50  res_num_sel_changes:                    0
% 7.68/1.50  res_moves_from_active_to_pass:          0
% 7.68/1.50  
% 7.68/1.50  ------ Superposition
% 7.68/1.50  
% 7.68/1.50  sup_time_total:                         0.
% 7.68/1.50  sup_time_generating:                    0.
% 7.68/1.50  sup_time_sim_full:                      0.
% 7.68/1.50  sup_time_sim_immed:                     0.
% 7.68/1.50  
% 7.68/1.50  sup_num_of_clauses:                     877
% 7.68/1.50  sup_num_in_active:                      168
% 7.68/1.50  sup_num_in_passive:                     709
% 7.68/1.50  sup_num_of_loops:                       313
% 7.68/1.50  sup_fw_superposition:                   816
% 7.68/1.50  sup_bw_superposition:                   897
% 7.68/1.50  sup_immediate_simplified:               587
% 7.68/1.50  sup_given_eliminated:                   3
% 7.68/1.50  comparisons_done:                       0
% 7.68/1.50  comparisons_avoided:                    19
% 7.68/1.50  
% 7.68/1.50  ------ Simplifications
% 7.68/1.50  
% 7.68/1.50  
% 7.68/1.50  sim_fw_subset_subsumed:                 99
% 7.68/1.50  sim_bw_subset_subsumed:                 100
% 7.68/1.50  sim_fw_subsumed:                        226
% 7.68/1.50  sim_bw_subsumed:                        11
% 7.68/1.50  sim_fw_subsumption_res:                 7
% 7.68/1.50  sim_bw_subsumption_res:                 0
% 7.68/1.50  sim_tautology_del:                      65
% 7.68/1.50  sim_eq_tautology_del:                   37
% 7.68/1.50  sim_eq_res_simp:                        8
% 7.68/1.50  sim_fw_demodulated:                     104
% 7.68/1.50  sim_bw_demodulated:                     131
% 7.68/1.50  sim_light_normalised:                   246
% 7.68/1.50  sim_joinable_taut:                      0
% 7.68/1.50  sim_joinable_simp:                      0
% 7.68/1.50  sim_ac_normalised:                      0
% 7.68/1.50  sim_smt_subsumption:                    0
% 7.68/1.50  
%------------------------------------------------------------------------------
