%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:32 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  241 (2900 expanded)
%              Number of clauses        :  160 (1039 expanded)
%              Number of leaves         :   22 ( 542 expanded)
%              Depth                    :   22
%              Number of atoms          :  665 (15422 expanded)
%              Number of equality atoms :  405 (5172 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f52])).

fof(f85,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_932,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_934,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_33])).

cnf(c_2244,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2248,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4357,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2244,c_2248])).

cnf(c_4715,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_934,c_4357])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2247,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3925,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2244,c_2247])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2245,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4114,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3925,c_2245])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2246,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3437,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2244,c_2246])).

cnf(c_4359,plain,
    ( k1_relset_1(sK1,X0,sK4) = k1_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_2248])).

cnf(c_4839,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4114,c_4359])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_183,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_35])).

cnf(c_184,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_184])).

cnf(c_919,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_2237,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_4846,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4839,c_2237])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2633,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r1_tarski(k2_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3123,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_3124,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3123])).

cnf(c_4901,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4846,c_38,c_3124,c_4114])).

cnf(c_4902,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4901])).

cnf(c_4905,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4715,c_4902])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3113,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2244,c_2255])).

cnf(c_4910,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4905,c_3113])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4927,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4910,c_5])).

cnf(c_93,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_95,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_34])).

cnf(c_943,plain,
    ( sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2257,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2257,c_8])).

cnf(c_2443,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2506,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2507,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2506])).

cnf(c_1596,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2523,plain,
    ( sK2 != X0
    | sK2 = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_2524,plain,
    ( sK2 = sK3
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_1595,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2608,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_1597,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2552,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_2770,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4),X2)
    | X2 != X1
    | k2_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_2771,plain,
    ( X0 != X1
    | k2_relat_1(sK4) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_2773,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_2817,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_3625,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_2255])).

cnf(c_3706,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_3625])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2250,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4719,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4715,c_2250])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4915,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4905,c_31])).

cnf(c_5029,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4915,c_4114])).

cnf(c_5142,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4927,c_38,c_95,c_103,c_104,c_943,c_2443,c_2507,c_2524,c_2608,c_2773,c_2817,c_3124,c_3706,c_4114,c_4719,c_5029])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2259,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2254,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2258,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3106,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_2258])).

cnf(c_3320,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2259,c_3106])).

cnf(c_4616,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3320,c_2250])).

cnf(c_94,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_108,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19,c_18])).

cnf(c_454,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_2442,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2271])).

cnf(c_2444,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2503,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_2671,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_2673,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_3108,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3106])).

cnf(c_6462,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4616,c_94,c_103,c_104,c_108,c_454,c_2444,c_2503,c_2673,c_3108])).

cnf(c_2249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3522,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2249])).

cnf(c_3550,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_3522])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2253,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3964,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3550,c_2253])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_16])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_20,c_19,c_16])).

cnf(c_2242,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2906,plain,
    ( k7_relat_1(k2_zfmisc_1(X0,X1),X0) = k2_zfmisc_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_2271,c_2242])).

cnf(c_2958,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_2906])).

cnf(c_2964,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2958,c_5])).

cnf(c_3972,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3964,c_2964])).

cnf(c_6467,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6462,c_3972])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2252,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6779,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6467,c_2252])).

cnf(c_6780,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6779,c_3320])).

cnf(c_69,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_2502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_2504,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_2672,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2671])).

cnf(c_2674,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_7992,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6780,c_71,c_95,c_103,c_104,c_2443,c_2504,c_2674])).

cnf(c_7993,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7992])).

cnf(c_7999,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5142,c_7993])).

cnf(c_4914,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4905,c_2244])).

cnf(c_4922,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4914,c_5])).

cnf(c_3624,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_3437])).

cnf(c_5280,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4922,c_38,c_95,c_103,c_104,c_943,c_2443,c_2507,c_2524,c_2608,c_2773,c_2817,c_3124,c_3624,c_4114,c_4719,c_5029])).

cnf(c_4361,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2248])).

cnf(c_5288,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5280,c_4361])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_184])).

cnf(c_890,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_2239,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_2400,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2239,c_6])).

cnf(c_5905,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5288,c_2400])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_906,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_2238,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_2370,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2238,c_6])).

cnf(c_5906,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5288,c_2370])).

cnf(c_5917,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5905,c_5906])).

cnf(c_24,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_846,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_184])).

cnf(c_847,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_2241,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_2409,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2241,c_5])).

cnf(c_2415,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2409,c_2271])).

cnf(c_5030,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4915,c_2415])).

cnf(c_5053,plain,
    ( sK4 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5030,c_38,c_3124,c_4114])).

cnf(c_5054,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5053])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7999,c_5917,c_5280,c_5054,c_4114,c_3124,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.36/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.99  
% 3.36/0.99  ------  iProver source info
% 3.36/0.99  
% 3.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.99  git: non_committed_changes: false
% 3.36/0.99  git: last_make_outside_of_git: false
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  
% 3.36/0.99  ------ Input Options
% 3.36/0.99  
% 3.36/0.99  --out_options                           all
% 3.36/0.99  --tptp_safe_out                         true
% 3.36/0.99  --problem_path                          ""
% 3.36/0.99  --include_path                          ""
% 3.36/0.99  --clausifier                            res/vclausify_rel
% 3.36/0.99  --clausifier_options                    --mode clausify
% 3.36/0.99  --stdin                                 false
% 3.36/0.99  --stats_out                             all
% 3.36/0.99  
% 3.36/0.99  ------ General Options
% 3.36/0.99  
% 3.36/0.99  --fof                                   false
% 3.36/0.99  --time_out_real                         305.
% 3.36/0.99  --time_out_virtual                      -1.
% 3.36/0.99  --symbol_type_check                     false
% 3.36/0.99  --clausify_out                          false
% 3.36/0.99  --sig_cnt_out                           false
% 3.36/0.99  --trig_cnt_out                          false
% 3.36/0.99  --trig_cnt_out_tolerance                1.
% 3.36/0.99  --trig_cnt_out_sk_spl                   false
% 3.36/0.99  --abstr_cl_out                          false
% 3.36/0.99  
% 3.36/0.99  ------ Global Options
% 3.36/0.99  
% 3.36/0.99  --schedule                              default
% 3.36/0.99  --add_important_lit                     false
% 3.36/0.99  --prop_solver_per_cl                    1000
% 3.36/0.99  --min_unsat_core                        false
% 3.36/0.99  --soft_assumptions                      false
% 3.36/0.99  --soft_lemma_size                       3
% 3.36/0.99  --prop_impl_unit_size                   0
% 3.36/0.99  --prop_impl_unit                        []
% 3.36/0.99  --share_sel_clauses                     true
% 3.36/0.99  --reset_solvers                         false
% 3.36/0.99  --bc_imp_inh                            [conj_cone]
% 3.36/0.99  --conj_cone_tolerance                   3.
% 3.36/0.99  --extra_neg_conj                        none
% 3.36/0.99  --large_theory_mode                     true
% 3.36/0.99  --prolific_symb_bound                   200
% 3.36/0.99  --lt_threshold                          2000
% 3.36/0.99  --clause_weak_htbl                      true
% 3.36/0.99  --gc_record_bc_elim                     false
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing Options
% 3.36/0.99  
% 3.36/0.99  --preprocessing_flag                    true
% 3.36/0.99  --time_out_prep_mult                    0.1
% 3.36/0.99  --splitting_mode                        input
% 3.36/0.99  --splitting_grd                         true
% 3.36/0.99  --splitting_cvd                         false
% 3.36/0.99  --splitting_cvd_svl                     false
% 3.36/0.99  --splitting_nvd                         32
% 3.36/0.99  --sub_typing                            true
% 3.36/0.99  --prep_gs_sim                           true
% 3.36/0.99  --prep_unflatten                        true
% 3.36/0.99  --prep_res_sim                          true
% 3.36/0.99  --prep_upred                            true
% 3.36/0.99  --prep_sem_filter                       exhaustive
% 3.36/0.99  --prep_sem_filter_out                   false
% 3.36/0.99  --pred_elim                             true
% 3.36/0.99  --res_sim_input                         true
% 3.36/0.99  --eq_ax_congr_red                       true
% 3.36/0.99  --pure_diseq_elim                       true
% 3.36/0.99  --brand_transform                       false
% 3.36/0.99  --non_eq_to_eq                          false
% 3.36/0.99  --prep_def_merge                        true
% 3.36/0.99  --prep_def_merge_prop_impl              false
% 3.36/0.99  --prep_def_merge_mbd                    true
% 3.36/0.99  --prep_def_merge_tr_red                 false
% 3.36/0.99  --prep_def_merge_tr_cl                  false
% 3.36/0.99  --smt_preprocessing                     true
% 3.36/0.99  --smt_ac_axioms                         fast
% 3.36/0.99  --preprocessed_out                      false
% 3.36/0.99  --preprocessed_stats                    false
% 3.36/0.99  
% 3.36/0.99  ------ Abstraction refinement Options
% 3.36/0.99  
% 3.36/0.99  --abstr_ref                             []
% 3.36/0.99  --abstr_ref_prep                        false
% 3.36/0.99  --abstr_ref_until_sat                   false
% 3.36/0.99  --abstr_ref_sig_restrict                funpre
% 3.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.99  --abstr_ref_under                       []
% 3.36/0.99  
% 3.36/0.99  ------ SAT Options
% 3.36/0.99  
% 3.36/0.99  --sat_mode                              false
% 3.36/0.99  --sat_fm_restart_options                ""
% 3.36/0.99  --sat_gr_def                            false
% 3.36/0.99  --sat_epr_types                         true
% 3.36/0.99  --sat_non_cyclic_types                  false
% 3.36/0.99  --sat_finite_models                     false
% 3.36/0.99  --sat_fm_lemmas                         false
% 3.36/0.99  --sat_fm_prep                           false
% 3.36/0.99  --sat_fm_uc_incr                        true
% 3.36/0.99  --sat_out_model                         small
% 3.36/0.99  --sat_out_clauses                       false
% 3.36/0.99  
% 3.36/0.99  ------ QBF Options
% 3.36/0.99  
% 3.36/0.99  --qbf_mode                              false
% 3.36/0.99  --qbf_elim_univ                         false
% 3.36/0.99  --qbf_dom_inst                          none
% 3.36/0.99  --qbf_dom_pre_inst                      false
% 3.36/0.99  --qbf_sk_in                             false
% 3.36/0.99  --qbf_pred_elim                         true
% 3.36/0.99  --qbf_split                             512
% 3.36/0.99  
% 3.36/0.99  ------ BMC1 Options
% 3.36/0.99  
% 3.36/0.99  --bmc1_incremental                      false
% 3.36/0.99  --bmc1_axioms                           reachable_all
% 3.36/0.99  --bmc1_min_bound                        0
% 3.36/0.99  --bmc1_max_bound                        -1
% 3.36/0.99  --bmc1_max_bound_default                -1
% 3.36/0.99  --bmc1_symbol_reachability              true
% 3.36/0.99  --bmc1_property_lemmas                  false
% 3.36/0.99  --bmc1_k_induction                      false
% 3.36/0.99  --bmc1_non_equiv_states                 false
% 3.36/0.99  --bmc1_deadlock                         false
% 3.36/0.99  --bmc1_ucm                              false
% 3.36/0.99  --bmc1_add_unsat_core                   none
% 3.36/0.99  --bmc1_unsat_core_children              false
% 3.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.99  --bmc1_out_stat                         full
% 3.36/0.99  --bmc1_ground_init                      false
% 3.36/0.99  --bmc1_pre_inst_next_state              false
% 3.36/0.99  --bmc1_pre_inst_state                   false
% 3.36/0.99  --bmc1_pre_inst_reach_state             false
% 3.36/0.99  --bmc1_out_unsat_core                   false
% 3.36/0.99  --bmc1_aig_witness_out                  false
% 3.36/0.99  --bmc1_verbose                          false
% 3.36/0.99  --bmc1_dump_clauses_tptp                false
% 3.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.99  --bmc1_dump_file                        -
% 3.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.99  --bmc1_ucm_extend_mode                  1
% 3.36/0.99  --bmc1_ucm_init_mode                    2
% 3.36/0.99  --bmc1_ucm_cone_mode                    none
% 3.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.99  --bmc1_ucm_relax_model                  4
% 3.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.99  --bmc1_ucm_layered_model                none
% 3.36/0.99  --bmc1_ucm_max_lemma_size               10
% 3.36/0.99  
% 3.36/0.99  ------ AIG Options
% 3.36/0.99  
% 3.36/0.99  --aig_mode                              false
% 3.36/0.99  
% 3.36/0.99  ------ Instantiation Options
% 3.36/0.99  
% 3.36/0.99  --instantiation_flag                    true
% 3.36/0.99  --inst_sos_flag                         false
% 3.36/0.99  --inst_sos_phase                        true
% 3.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.99  --inst_lit_sel_side                     num_symb
% 3.36/0.99  --inst_solver_per_active                1400
% 3.36/0.99  --inst_solver_calls_frac                1.
% 3.36/0.99  --inst_passive_queue_type               priority_queues
% 3.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.99  --inst_passive_queues_freq              [25;2]
% 3.36/0.99  --inst_dismatching                      true
% 3.36/0.99  --inst_eager_unprocessed_to_passive     true
% 3.36/0.99  --inst_prop_sim_given                   true
% 3.36/0.99  --inst_prop_sim_new                     false
% 3.36/0.99  --inst_subs_new                         false
% 3.36/0.99  --inst_eq_res_simp                      false
% 3.36/0.99  --inst_subs_given                       false
% 3.36/0.99  --inst_orphan_elimination               true
% 3.36/0.99  --inst_learning_loop_flag               true
% 3.36/0.99  --inst_learning_start                   3000
% 3.36/0.99  --inst_learning_factor                  2
% 3.36/0.99  --inst_start_prop_sim_after_learn       3
% 3.36/0.99  --inst_sel_renew                        solver
% 3.36/0.99  --inst_lit_activity_flag                true
% 3.36/0.99  --inst_restr_to_given                   false
% 3.36/0.99  --inst_activity_threshold               500
% 3.36/0.99  --inst_out_proof                        true
% 3.36/0.99  
% 3.36/0.99  ------ Resolution Options
% 3.36/0.99  
% 3.36/0.99  --resolution_flag                       true
% 3.36/0.99  --res_lit_sel                           adaptive
% 3.36/0.99  --res_lit_sel_side                      none
% 3.36/0.99  --res_ordering                          kbo
% 3.36/0.99  --res_to_prop_solver                    active
% 3.36/0.99  --res_prop_simpl_new                    false
% 3.36/0.99  --res_prop_simpl_given                  true
% 3.36/0.99  --res_passive_queue_type                priority_queues
% 3.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.99  --res_passive_queues_freq               [15;5]
% 3.36/0.99  --res_forward_subs                      full
% 3.36/0.99  --res_backward_subs                     full
% 3.36/0.99  --res_forward_subs_resolution           true
% 3.36/0.99  --res_backward_subs_resolution          true
% 3.36/0.99  --res_orphan_elimination                true
% 3.36/0.99  --res_time_limit                        2.
% 3.36/0.99  --res_out_proof                         true
% 3.36/0.99  
% 3.36/0.99  ------ Superposition Options
% 3.36/0.99  
% 3.36/0.99  --superposition_flag                    true
% 3.36/0.99  --sup_passive_queue_type                priority_queues
% 3.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.99  --demod_completeness_check              fast
% 3.36/0.99  --demod_use_ground                      true
% 3.36/0.99  --sup_to_prop_solver                    passive
% 3.36/0.99  --sup_prop_simpl_new                    true
% 3.36/0.99  --sup_prop_simpl_given                  true
% 3.36/0.99  --sup_fun_splitting                     false
% 3.36/0.99  --sup_smt_interval                      50000
% 3.36/0.99  
% 3.36/0.99  ------ Superposition Simplification Setup
% 3.36/0.99  
% 3.36/0.99  --sup_indices_passive                   []
% 3.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.99  --sup_full_bw                           [BwDemod]
% 3.36/0.99  --sup_immed_triv                        [TrivRules]
% 3.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.99  --sup_immed_bw_main                     []
% 3.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.99  
% 3.36/0.99  ------ Combination Options
% 3.36/0.99  
% 3.36/0.99  --comb_res_mult                         3
% 3.36/0.99  --comb_sup_mult                         2
% 3.36/0.99  --comb_inst_mult                        10
% 3.36/0.99  
% 3.36/0.99  ------ Debug Options
% 3.36/0.99  
% 3.36/0.99  --dbg_backtrace                         false
% 3.36/0.99  --dbg_dump_prop_clauses                 false
% 3.36/0.99  --dbg_dump_prop_clauses_file            -
% 3.36/0.99  --dbg_out_stat                          false
% 3.36/0.99  ------ Parsing...
% 3.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.99  ------ Proving...
% 3.36/0.99  ------ Problem Properties 
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  clauses                                 33
% 3.36/0.99  conjectures                             3
% 3.36/0.99  EPR                                     5
% 3.36/0.99  Horn                                    29
% 3.36/0.99  unary                                   7
% 3.36/0.99  binary                                  14
% 3.36/0.99  lits                                    76
% 3.36/0.99  lits eq                                 34
% 3.36/0.99  fd_pure                                 0
% 3.36/0.99  fd_pseudo                               0
% 3.36/0.99  fd_cond                                 3
% 3.36/0.99  fd_pseudo_cond                          0
% 3.36/0.99  AC symbols                              0
% 3.36/0.99  
% 3.36/0.99  ------ Schedule dynamic 5 is on 
% 3.36/0.99  
% 3.36/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  Current options:
% 3.36/0.99  ------ 
% 3.36/0.99  
% 3.36/0.99  ------ Input Options
% 3.36/0.99  
% 3.36/0.99  --out_options                           all
% 3.36/0.99  --tptp_safe_out                         true
% 3.36/0.99  --problem_path                          ""
% 3.36/0.99  --include_path                          ""
% 3.36/0.99  --clausifier                            res/vclausify_rel
% 3.36/0.99  --clausifier_options                    --mode clausify
% 3.36/0.99  --stdin                                 false
% 3.36/0.99  --stats_out                             all
% 3.36/0.99  
% 3.36/0.99  ------ General Options
% 3.36/0.99  
% 3.36/0.99  --fof                                   false
% 3.36/0.99  --time_out_real                         305.
% 3.36/0.99  --time_out_virtual                      -1.
% 3.36/0.99  --symbol_type_check                     false
% 3.36/0.99  --clausify_out                          false
% 3.36/0.99  --sig_cnt_out                           false
% 3.36/0.99  --trig_cnt_out                          false
% 3.36/0.99  --trig_cnt_out_tolerance                1.
% 3.36/0.99  --trig_cnt_out_sk_spl                   false
% 3.36/0.99  --abstr_cl_out                          false
% 3.36/0.99  
% 3.36/0.99  ------ Global Options
% 3.36/0.99  
% 3.36/0.99  --schedule                              default
% 3.36/0.99  --add_important_lit                     false
% 3.36/0.99  --prop_solver_per_cl                    1000
% 3.36/0.99  --min_unsat_core                        false
% 3.36/0.99  --soft_assumptions                      false
% 3.36/0.99  --soft_lemma_size                       3
% 3.36/0.99  --prop_impl_unit_size                   0
% 3.36/0.99  --prop_impl_unit                        []
% 3.36/0.99  --share_sel_clauses                     true
% 3.36/0.99  --reset_solvers                         false
% 3.36/0.99  --bc_imp_inh                            [conj_cone]
% 3.36/0.99  --conj_cone_tolerance                   3.
% 3.36/0.99  --extra_neg_conj                        none
% 3.36/0.99  --large_theory_mode                     true
% 3.36/0.99  --prolific_symb_bound                   200
% 3.36/0.99  --lt_threshold                          2000
% 3.36/0.99  --clause_weak_htbl                      true
% 3.36/0.99  --gc_record_bc_elim                     false
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing Options
% 3.36/0.99  
% 3.36/0.99  --preprocessing_flag                    true
% 3.36/0.99  --time_out_prep_mult                    0.1
% 3.36/0.99  --splitting_mode                        input
% 3.36/0.99  --splitting_grd                         true
% 3.36/0.99  --splitting_cvd                         false
% 3.36/0.99  --splitting_cvd_svl                     false
% 3.36/0.99  --splitting_nvd                         32
% 3.36/0.99  --sub_typing                            true
% 3.36/0.99  --prep_gs_sim                           true
% 3.36/0.99  --prep_unflatten                        true
% 3.36/0.99  --prep_res_sim                          true
% 3.36/0.99  --prep_upred                            true
% 3.36/0.99  --prep_sem_filter                       exhaustive
% 3.36/0.99  --prep_sem_filter_out                   false
% 3.36/0.99  --pred_elim                             true
% 3.36/0.99  --res_sim_input                         true
% 3.36/0.99  --eq_ax_congr_red                       true
% 3.36/0.99  --pure_diseq_elim                       true
% 3.36/0.99  --brand_transform                       false
% 3.36/0.99  --non_eq_to_eq                          false
% 3.36/0.99  --prep_def_merge                        true
% 3.36/0.99  --prep_def_merge_prop_impl              false
% 3.36/0.99  --prep_def_merge_mbd                    true
% 3.36/0.99  --prep_def_merge_tr_red                 false
% 3.36/0.99  --prep_def_merge_tr_cl                  false
% 3.36/0.99  --smt_preprocessing                     true
% 3.36/0.99  --smt_ac_axioms                         fast
% 3.36/0.99  --preprocessed_out                      false
% 3.36/0.99  --preprocessed_stats                    false
% 3.36/0.99  
% 3.36/0.99  ------ Abstraction refinement Options
% 3.36/0.99  
% 3.36/0.99  --abstr_ref                             []
% 3.36/0.99  --abstr_ref_prep                        false
% 3.36/0.99  --abstr_ref_until_sat                   false
% 3.36/0.99  --abstr_ref_sig_restrict                funpre
% 3.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.99  --abstr_ref_under                       []
% 3.36/0.99  
% 3.36/0.99  ------ SAT Options
% 3.36/0.99  
% 3.36/0.99  --sat_mode                              false
% 3.36/0.99  --sat_fm_restart_options                ""
% 3.36/0.99  --sat_gr_def                            false
% 3.36/0.99  --sat_epr_types                         true
% 3.36/0.99  --sat_non_cyclic_types                  false
% 3.36/0.99  --sat_finite_models                     false
% 3.36/0.99  --sat_fm_lemmas                         false
% 3.36/0.99  --sat_fm_prep                           false
% 3.36/0.99  --sat_fm_uc_incr                        true
% 3.36/0.99  --sat_out_model                         small
% 3.36/0.99  --sat_out_clauses                       false
% 3.36/0.99  
% 3.36/0.99  ------ QBF Options
% 3.36/0.99  
% 3.36/0.99  --qbf_mode                              false
% 3.36/0.99  --qbf_elim_univ                         false
% 3.36/0.99  --qbf_dom_inst                          none
% 3.36/0.99  --qbf_dom_pre_inst                      false
% 3.36/0.99  --qbf_sk_in                             false
% 3.36/0.99  --qbf_pred_elim                         true
% 3.36/0.99  --qbf_split                             512
% 3.36/0.99  
% 3.36/0.99  ------ BMC1 Options
% 3.36/0.99  
% 3.36/0.99  --bmc1_incremental                      false
% 3.36/0.99  --bmc1_axioms                           reachable_all
% 3.36/0.99  --bmc1_min_bound                        0
% 3.36/0.99  --bmc1_max_bound                        -1
% 3.36/0.99  --bmc1_max_bound_default                -1
% 3.36/0.99  --bmc1_symbol_reachability              true
% 3.36/0.99  --bmc1_property_lemmas                  false
% 3.36/0.99  --bmc1_k_induction                      false
% 3.36/0.99  --bmc1_non_equiv_states                 false
% 3.36/0.99  --bmc1_deadlock                         false
% 3.36/0.99  --bmc1_ucm                              false
% 3.36/0.99  --bmc1_add_unsat_core                   none
% 3.36/0.99  --bmc1_unsat_core_children              false
% 3.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.99  --bmc1_out_stat                         full
% 3.36/0.99  --bmc1_ground_init                      false
% 3.36/0.99  --bmc1_pre_inst_next_state              false
% 3.36/0.99  --bmc1_pre_inst_state                   false
% 3.36/0.99  --bmc1_pre_inst_reach_state             false
% 3.36/0.99  --bmc1_out_unsat_core                   false
% 3.36/0.99  --bmc1_aig_witness_out                  false
% 3.36/0.99  --bmc1_verbose                          false
% 3.36/0.99  --bmc1_dump_clauses_tptp                false
% 3.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.99  --bmc1_dump_file                        -
% 3.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.99  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     none
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       false
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS status Theorem for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  fof(f19,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f39,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f19])).
% 3.36/1.00  
% 3.36/1.00  fof(f40,plain,(
% 3.36/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(flattening,[],[f39])).
% 3.36/1.00  
% 3.36/1.00  fof(f51,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(nnf_transformation,[],[f40])).
% 3.36/1.00  
% 3.36/1.00  fof(f78,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f51])).
% 3.36/1.00  
% 3.36/1.00  fof(f20,conjecture,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f21,negated_conjecture,(
% 3.36/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.36/1.00    inference(negated_conjecture,[],[f20])).
% 3.36/1.00  
% 3.36/1.00  fof(f41,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.36/1.00    inference(ennf_transformation,[],[f21])).
% 3.36/1.00  
% 3.36/1.00  fof(f42,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.36/1.00    inference(flattening,[],[f41])).
% 3.36/1.00  
% 3.36/1.00  fof(f52,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.36/1.00    introduced(choice_axiom,[])).
% 3.36/1.00  
% 3.36/1.00  fof(f53,plain,(
% 3.36/1.00    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f52])).
% 3.36/1.00  
% 3.36/1.00  fof(f85,plain,(
% 3.36/1.00    v1_funct_2(sK4,sK1,sK2)),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f86,plain,(
% 3.36/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f16,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f35,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f16])).
% 3.36/1.00  
% 3.36/1.00  fof(f75,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f35])).
% 3.36/1.00  
% 3.36/1.00  fof(f17,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f36,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f17])).
% 3.36/1.00  
% 3.36/1.00  fof(f76,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f36])).
% 3.36/1.00  
% 3.36/1.00  fof(f87,plain,(
% 3.36/1.00    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f18,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f37,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.36/1.00    inference(ennf_transformation,[],[f18])).
% 3.36/1.00  
% 3.36/1.00  fof(f38,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.36/1.00    inference(flattening,[],[f37])).
% 3.36/1.00  
% 3.36/1.00  fof(f77,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f38])).
% 3.36/1.00  
% 3.36/1.00  fof(f80,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f51])).
% 3.36/1.00  
% 3.36/1.00  fof(f89,plain,(
% 3.36/1.00    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f84,plain,(
% 3.36/1.00    v1_funct_1(sK4)),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f7,axiom,(
% 3.36/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f49,plain,(
% 3.36/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.36/1.00    inference(nnf_transformation,[],[f7])).
% 3.36/1.00  
% 3.36/1.00  fof(f64,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f49])).
% 3.36/1.00  
% 3.36/1.00  fof(f4,axiom,(
% 3.36/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f47,plain,(
% 3.36/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/1.00    inference(nnf_transformation,[],[f4])).
% 3.36/1.00  
% 3.36/1.00  fof(f48,plain,(
% 3.36/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/1.00    inference(flattening,[],[f47])).
% 3.36/1.00  
% 3.36/1.00  fof(f61,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.36/1.00    inference(cnf_transformation,[],[f48])).
% 3.36/1.00  
% 3.36/1.00  fof(f90,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.36/1.00    inference(equality_resolution,[],[f61])).
% 3.36/1.00  
% 3.36/1.00  fof(f59,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f48])).
% 3.36/1.00  
% 3.36/1.00  fof(f60,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.36/1.00    inference(cnf_transformation,[],[f48])).
% 3.36/1.00  
% 3.36/1.00  fof(f91,plain,(
% 3.36/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.36/1.00    inference(equality_resolution,[],[f60])).
% 3.36/1.00  
% 3.36/1.00  fof(f6,axiom,(
% 3.36/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f63,plain,(
% 3.36/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f6])).
% 3.36/1.00  
% 3.36/1.00  fof(f5,axiom,(
% 3.36/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f62,plain,(
% 3.36/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.36/1.00    inference(cnf_transformation,[],[f5])).
% 3.36/1.00  
% 3.36/1.00  fof(f14,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f33,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f14])).
% 3.36/1.00  
% 3.36/1.00  fof(f73,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f33])).
% 3.36/1.00  
% 3.36/1.00  fof(f13,axiom,(
% 3.36/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f32,plain,(
% 3.36/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f13])).
% 3.36/1.00  
% 3.36/1.00  fof(f50,plain,(
% 3.36/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(nnf_transformation,[],[f32])).
% 3.36/1.00  
% 3.36/1.00  fof(f71,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f88,plain,(
% 3.36/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.36/1.00    inference(cnf_transformation,[],[f53])).
% 3.36/1.00  
% 3.36/1.00  fof(f2,axiom,(
% 3.36/1.00    v1_xboole_0(k1_xboole_0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f57,plain,(
% 3.36/1.00    v1_xboole_0(k1_xboole_0)),
% 3.36/1.00    inference(cnf_transformation,[],[f2])).
% 3.36/1.00  
% 3.36/1.00  fof(f9,axiom,(
% 3.36/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f26,plain,(
% 3.36/1.00    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f9])).
% 3.36/1.00  
% 3.36/1.00  fof(f67,plain,(
% 3.36/1.00    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f26])).
% 3.36/1.00  
% 3.36/1.00  fof(f3,axiom,(
% 3.36/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f24,plain,(
% 3.36/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f3])).
% 3.36/1.00  
% 3.36/1.00  fof(f58,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f24])).
% 3.36/1.00  
% 3.36/1.00  fof(f65,plain,(
% 3.36/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f49])).
% 3.36/1.00  
% 3.36/1.00  fof(f10,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f27,plain,(
% 3.36/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f10])).
% 3.36/1.00  
% 3.36/1.00  fof(f68,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f27])).
% 3.36/1.00  
% 3.36/1.00  fof(f15,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f22,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.36/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.36/1.00  
% 3.36/1.00  fof(f34,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f22])).
% 3.36/1.00  
% 3.36/1.00  fof(f74,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f12,axiom,(
% 3.36/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f30,plain,(
% 3.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.36/1.00    inference(ennf_transformation,[],[f12])).
% 3.36/1.00  
% 3.36/1.00  fof(f31,plain,(
% 3.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f30])).
% 3.36/1.00  
% 3.36/1.00  fof(f70,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f31])).
% 3.36/1.00  
% 3.36/1.00  fof(f11,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f28,plain,(
% 3.36/1.00    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f11])).
% 3.36/1.00  
% 3.36/1.00  fof(f29,plain,(
% 3.36/1.00    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f28])).
% 3.36/1.00  
% 3.36/1.00  fof(f69,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f29])).
% 3.36/1.00  
% 3.36/1.00  fof(f81,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f51])).
% 3.36/1.00  
% 3.36/1.00  fof(f95,plain,(
% 3.36/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.36/1.00    inference(equality_resolution,[],[f81])).
% 3.36/1.00  
% 3.36/1.00  fof(f79,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f51])).
% 3.36/1.00  
% 3.36/1.00  fof(f96,plain,(
% 3.36/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.36/1.00    inference(equality_resolution,[],[f79])).
% 3.36/1.00  
% 3.36/1.00  fof(f83,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f51])).
% 3.36/1.00  
% 3.36/1.00  fof(f92,plain,(
% 3.36/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(equality_resolution,[],[f83])).
% 3.36/1.00  
% 3.36/1.00  fof(f93,plain,(
% 3.36/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.36/1.00    inference(equality_resolution,[],[f92])).
% 3.36/1.00  
% 3.36/1.00  cnf(c_29,plain,
% 3.36/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_34,negated_conjecture,
% 3.36/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.36/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_931,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.36/1.00      | sK2 != X2
% 3.36/1.00      | sK1 != X1
% 3.36/1.00      | sK4 != X0
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_932,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.36/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.36/1.00      | k1_xboole_0 = sK2 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_931]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_33,negated_conjecture,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_934,plain,
% 3.36/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_932,c_33]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2244,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_21,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2248,plain,
% 3.36/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4357,plain,
% 3.36/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2244,c_2248]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4715,plain,
% 3.36/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_934,c_4357]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_22,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2247,plain,
% 3.36/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3925,plain,
% 3.36/1.00      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2244,c_2247]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_32,negated_conjecture,
% 3.36/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2245,plain,
% 3.36/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4114,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_3925,c_2245]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_23,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2246,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3437,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2244,c_2246]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4359,plain,
% 3.36/1.00      ( k1_relset_1(sK1,X0,sK4) = k1_relat_1(sK4)
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3437,c_2248]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4839,plain,
% 3.36/1.00      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4114,c_4359]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_27,plain,
% 3.36/1.00      ( v1_funct_2(X0,X1,X2)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_30,negated_conjecture,
% 3.36/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ v1_funct_1(sK4) ),
% 3.36/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_35,negated_conjecture,
% 3.36/1.00      ( v1_funct_1(sK4) ),
% 3.36/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_183,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_30,c_35]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_184,negated_conjecture,
% 3.36/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_183]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_918,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.36/1.00      | sK3 != X2
% 3.36/1.00      | sK1 != X1
% 3.36/1.00      | sK4 != X0
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_184]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_919,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.36/1.00      | k1_xboole_0 = sK3 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_918]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2237,plain,
% 3.36/1.00      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.36/1.00      | k1_xboole_0 = sK3
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4846,plain,
% 3.36/1.00      ( k1_relat_1(sK4) != sK1
% 3.36/1.00      | sK3 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4839,c_2237]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_38,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2633,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3123,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2633]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3124,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_3123]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4901,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) != sK1 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4846,c_38,c_3124,c_4114]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4902,plain,
% 3.36/1.00      ( k1_relat_1(sK4) != sK1 | sK3 = k1_xboole_0 ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_4901]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4905,plain,
% 3.36/1.00      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4715,c_4902]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_11,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2255,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.36/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3113,plain,
% 3.36/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2244,c_2255]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4910,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0
% 3.36/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4905,c_3113]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5,plain,
% 3.36/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4927,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4910,c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_93,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.36/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_95,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.36/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_93]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7,plain,
% 3.36/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = X0
% 3.36/1.00      | k1_xboole_0 = X1 ),
% 3.36/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_103,plain,
% 3.36/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6,plain,
% 3.36/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_104,plain,
% 3.36/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_942,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | sK2 != sK3
% 3.36/1.00      | sK1 != sK1
% 3.36/1.00      | sK4 != sK4 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_184,c_34]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_943,plain,
% 3.36/1.00      ( sK2 != sK3
% 3.36/1.00      | sK1 != sK1
% 3.36/1.00      | sK4 != sK4
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_9,plain,
% 3.36/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2257,plain,
% 3.36/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8,plain,
% 3.36/1.00      ( k2_subset_1(X0) = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2271,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_2257,c_8]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2443,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2271]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_19,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2506,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.36/1.00      | v1_relat_1(sK4) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2507,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.36/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2506]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1596,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2523,plain,
% 3.36/1.00      ( sK2 != X0 | sK2 = sK3 | sK3 != X0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1596]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2524,plain,
% 3.36/1.00      ( sK2 = sK3 | sK2 != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2523]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1595,plain,( X0 = X0 ),theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2608,plain,
% 3.36/1.00      ( sK1 = sK1 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1597,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.36/1.00      theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2552,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1)
% 3.36/1.00      | r1_tarski(k2_relat_1(X2),X3)
% 3.36/1.00      | X3 != X1
% 3.36/1.00      | k2_relat_1(X2) != X0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2770,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1)
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),X2)
% 3.36/1.00      | X2 != X1
% 3.36/1.00      | k2_relat_1(sK4) != X0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2552]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2771,plain,
% 3.36/1.00      ( X0 != X1
% 3.36/1.00      | k2_relat_1(sK4) != X2
% 3.36/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2773,plain,
% 3.36/1.00      ( k2_relat_1(sK4) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 != k1_xboole_0
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
% 3.36/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2771]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2817,plain,
% 3.36/1.00      ( sK4 = sK4 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3625,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.36/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,X0)) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3437,c_2255]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3706,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.36/1.00      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5,c_3625]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_18,plain,
% 3.36/1.00      ( ~ v1_relat_1(X0)
% 3.36/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.36/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2250,plain,
% 3.36/1.00      ( k2_relat_1(X0) = k1_xboole_0
% 3.36/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4719,plain,
% 3.36/1.00      ( k2_relat_1(sK4) = k1_xboole_0
% 3.36/1.00      | sK2 = k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4715,c_2250]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_31,negated_conjecture,
% 3.36/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.36/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4915,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4905,c_31]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5029,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4915,c_4114]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5142,plain,
% 3.36/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4927,c_38,c_95,c_103,c_104,c_943,c_2443,c_2507,c_2524,
% 3.36/1.00                 c_2608,c_2773,c_2817,c_3124,c_3706,c_4114,c_4719,c_5029]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3,plain,
% 3.36/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2259,plain,
% 3.36/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_13,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2254,plain,
% 3.36/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.36/1.00      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2258,plain,
% 3.36/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3106,plain,
% 3.36/1.00      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2254,c_2258]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3320,plain,
% 3.36/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2259,c_3106]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4616,plain,
% 3.36/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.36/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3320,c_2250]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_94,plain,
% 3.36/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.36/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_108,plain,
% 3.36/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_452,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.36/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.36/1.00      inference(resolution,[status(thm)],[c_19,c_18]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_454,plain,
% 3.36/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.36/1.00      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.36/1.00      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_452]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2442,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.36/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2271]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2444,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2442]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_10,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2501,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2503,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.36/1.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2501]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2671,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1)
% 3.36/1.00      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 3.36/1.00      | X2 != X0
% 3.36/1.00      | k2_zfmisc_1(X3,X4) != X1 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2673,plain,
% 3.36/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 3.36/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.36/1.00      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2671]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3108,plain,
% 3.36/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 3.36/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_3106]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6462,plain,
% 3.36/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4616,c_94,c_103,c_104,c_108,c_454,c_2444,c_2503,
% 3.36/1.00                 c_2673,c_3108]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2249,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3522,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5,c_2249]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3550,plain,
% 3.36/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2271,c_3522]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_14,plain,
% 3.36/1.00      ( ~ v1_relat_1(X0)
% 3.36/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2253,plain,
% 3.36/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3964,plain,
% 3.36/1.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3550,c_2253]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_20,plain,
% 3.36/1.00      ( v4_relat_1(X0,X1)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_16,plain,
% 3.36/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_432,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_relat_1(X0)
% 3.36/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(resolution,[status(thm)],[c_20,c_16]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_436,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_432,c_20,c_19,c_16]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2242,plain,
% 3.36/1.00      ( k7_relat_1(X0,X1) = X0
% 3.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2906,plain,
% 3.36/1.00      ( k7_relat_1(k2_zfmisc_1(X0,X1),X0) = k2_zfmisc_1(X0,X1) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2271,c_2242]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2958,plain,
% 3.36/1.00      ( k7_relat_1(k1_xboole_0,X0) = k2_zfmisc_1(X0,k1_xboole_0) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5,c_2906]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2964,plain,
% 3.36/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_2958,c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3972,plain,
% 3.36/1.00      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_3964,c_2964]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6467,plain,
% 3.36/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_6462,c_3972]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_15,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.36/1.00      | ~ v1_relat_1(X1)
% 3.36/1.00      | k9_relat_1(X1,X0) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2252,plain,
% 3.36/1.00      ( k9_relat_1(X0,X1) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = X1
% 3.36/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6779,plain,
% 3.36/1.00      ( k1_xboole_0 = X0
% 3.36/1.00      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.36/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_6467,c_2252]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6780,plain,
% 3.36/1.00      ( k1_xboole_0 = X0
% 3.36/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.36/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_6779,c_3320]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_69,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_71,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.36/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_69]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2502,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.36/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2504,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.36/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2502]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2672,plain,
% 3.36/1.00      ( X0 != X1
% 3.36/1.00      | k2_zfmisc_1(X2,X3) != X4
% 3.36/1.00      | r1_tarski(X1,X4) != iProver_top
% 3.36/1.00      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2671]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2674,plain,
% 3.36/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 != k1_xboole_0
% 3.36/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.36/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2672]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7992,plain,
% 3.36/1.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_6780,c_71,c_95,c_103,c_104,c_2443,c_2504,c_2674]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7993,plain,
% 3.36/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_7992]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7999,plain,
% 3.36/1.00      ( sK4 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5142,c_7993]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4914,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4905,c_2244]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4922,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4914,c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3624,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5,c_3437]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5280,plain,
% 3.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4922,c_38,c_95,c_103,c_104,c_943,c_2443,c_2507,c_2524,
% 3.36/1.00                 c_2608,c_2773,c_2817,c_3124,c_3624,c_4114,c_4719,c_5029]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4361,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.36/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_6,c_2248]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5288,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5280,c_4361]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_26,plain,
% 3.36/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_889,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.36/1.00      | sK3 != X1
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | sK4 != X0 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_184]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_890,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_889]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2239,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2400,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_2239,c_6]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5905,plain,
% 3.36/1.00      ( k1_relat_1(sK4) != k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_5288,c_2400]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_28,plain,
% 3.36/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_905,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.36/1.00      | sK2 != X1
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | sK4 != X0 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_906,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.36/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_905]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2238,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2370,plain,
% 3.36/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_2238,c_6]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5906,plain,
% 3.36/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.36/1.00      | sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_5288,c_2370]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5917,plain,
% 3.36/1.00      ( sK1 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(forward_subsumption_resolution,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5905,c_5906]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_24,plain,
% 3.36/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.36/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.36/1.00      | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_846,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.36/1.00      | sK3 != k1_xboole_0
% 3.36/1.00      | sK1 != X0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_184]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_847,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.36/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.36/1.00      | sK3 != k1_xboole_0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = sK1 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_846]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2241,plain,
% 3.36/1.00      ( sK3 != k1_xboole_0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = sK1
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2409,plain,
% 3.36/1.00      ( sK3 != k1_xboole_0
% 3.36/1.00      | sK1 = k1_xboole_0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.36/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_2241,c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2415,plain,
% 3.36/1.00      ( sK3 != k1_xboole_0
% 3.36/1.00      | sK1 = k1_xboole_0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.36/1.00      inference(forward_subsumption_resolution,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_2409,c_2271]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5030,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | sK4 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4915,c_2415]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5053,plain,
% 3.36/1.00      ( sK4 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5030,c_38,c_3124,c_4114]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5054,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_5053]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(contradiction,plain,
% 3.36/1.00      ( $false ),
% 3.36/1.00      inference(minisat,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_7999,c_5917,c_5280,c_5054,c_4114,c_3124,c_38]) ).
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  ------                               Statistics
% 3.36/1.00  
% 3.36/1.00  ------ General
% 3.36/1.00  
% 3.36/1.00  abstr_ref_over_cycles:                  0
% 3.36/1.00  abstr_ref_under_cycles:                 0
% 3.36/1.00  gc_basic_clause_elim:                   0
% 3.36/1.00  forced_gc_time:                         0
% 3.36/1.00  parsing_time:                           0.014
% 3.36/1.00  unif_index_cands_time:                  0.
% 3.36/1.00  unif_index_add_time:                    0.
% 3.36/1.00  orderings_time:                         0.
% 3.36/1.00  out_proof_time:                         0.016
% 3.36/1.00  total_time:                             0.275
% 3.36/1.00  num_of_symbols:                         54
% 3.36/1.00  num_of_terms:                           7680
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing
% 3.36/1.00  
% 3.36/1.00  num_of_splits:                          0
% 3.36/1.00  num_of_split_atoms:                     0
% 3.36/1.00  num_of_reused_defs:                     0
% 3.36/1.00  num_eq_ax_congr_red:                    34
% 3.36/1.00  num_of_sem_filtered_clauses:            2
% 3.36/1.00  num_of_subtypes:                        0
% 3.36/1.00  monotx_restored_types:                  0
% 3.36/1.00  sat_num_of_epr_types:                   0
% 3.36/1.00  sat_num_of_non_cyclic_types:            0
% 3.36/1.00  sat_guarded_non_collapsed_types:        0
% 3.36/1.00  num_pure_diseq_elim:                    0
% 3.36/1.00  simp_replaced_by:                       0
% 3.36/1.00  res_preprocessed:                       158
% 3.36/1.00  prep_upred:                             0
% 3.36/1.00  prep_unflattend:                        99
% 3.36/1.00  smt_new_axioms:                         0
% 3.36/1.00  pred_elim_cands:                        5
% 3.36/1.00  pred_elim:                              2
% 3.36/1.00  pred_elim_cl:                           2
% 3.36/1.00  pred_elim_cycles:                       7
% 3.36/1.00  merged_defs:                            8
% 3.36/1.00  merged_defs_ncl:                        0
% 3.36/1.00  bin_hyper_res:                          9
% 3.36/1.00  prep_cycles:                            4
% 3.36/1.00  pred_elim_time:                         0.016
% 3.36/1.00  splitting_time:                         0.
% 3.36/1.00  sem_filter_time:                        0.
% 3.36/1.00  monotx_time:                            0.001
% 3.36/1.00  subtype_inf_time:                       0.
% 3.36/1.00  
% 3.36/1.00  ------ Problem properties
% 3.36/1.00  
% 3.36/1.00  clauses:                                33
% 3.36/1.00  conjectures:                            3
% 3.36/1.00  epr:                                    5
% 3.36/1.00  horn:                                   29
% 3.36/1.00  ground:                                 11
% 3.36/1.00  unary:                                  7
% 3.36/1.00  binary:                                 14
% 3.36/1.00  lits:                                   76
% 3.36/1.00  lits_eq:                                34
% 3.36/1.00  fd_pure:                                0
% 3.36/1.00  fd_pseudo:                              0
% 3.36/1.00  fd_cond:                                3
% 3.36/1.00  fd_pseudo_cond:                         0
% 3.36/1.00  ac_symbols:                             0
% 3.36/1.00  
% 3.36/1.00  ------ Propositional Solver
% 3.36/1.00  
% 3.36/1.00  prop_solver_calls:                      29
% 3.36/1.00  prop_fast_solver_calls:                 1207
% 3.36/1.00  smt_solver_calls:                       0
% 3.36/1.00  smt_fast_solver_calls:                  0
% 3.36/1.00  prop_num_of_clauses:                    2997
% 3.36/1.00  prop_preprocess_simplified:             8755
% 3.36/1.00  prop_fo_subsumed:                       26
% 3.36/1.00  prop_solver_time:                       0.
% 3.36/1.00  smt_solver_time:                        0.
% 3.36/1.00  smt_fast_solver_time:                   0.
% 3.36/1.00  prop_fast_solver_time:                  0.
% 3.36/1.00  prop_unsat_core_time:                   0.
% 3.36/1.00  
% 3.36/1.00  ------ QBF
% 3.36/1.00  
% 3.36/1.00  qbf_q_res:                              0
% 3.36/1.00  qbf_num_tautologies:                    0
% 3.36/1.00  qbf_prep_cycles:                        0
% 3.36/1.00  
% 3.36/1.00  ------ BMC1
% 3.36/1.00  
% 3.36/1.00  bmc1_current_bound:                     -1
% 3.36/1.00  bmc1_last_solved_bound:                 -1
% 3.36/1.00  bmc1_unsat_core_size:                   -1
% 3.36/1.00  bmc1_unsat_core_parents_size:           -1
% 3.36/1.00  bmc1_merge_next_fun:                    0
% 3.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation
% 3.36/1.00  
% 3.36/1.00  inst_num_of_clauses:                    1233
% 3.36/1.00  inst_num_in_passive:                    239
% 3.36/1.00  inst_num_in_active:                     591
% 3.36/1.00  inst_num_in_unprocessed:                403
% 3.36/1.00  inst_num_of_loops:                      650
% 3.36/1.00  inst_num_of_learning_restarts:          0
% 3.36/1.00  inst_num_moves_active_passive:          56
% 3.36/1.00  inst_lit_activity:                      0
% 3.36/1.00  inst_lit_activity_moves:                0
% 3.36/1.00  inst_num_tautologies:                   0
% 3.36/1.00  inst_num_prop_implied:                  0
% 3.36/1.00  inst_num_existing_simplified:           0
% 3.36/1.00  inst_num_eq_res_simplified:             0
% 3.36/1.00  inst_num_child_elim:                    0
% 3.36/1.00  inst_num_of_dismatching_blockings:      285
% 3.36/1.00  inst_num_of_non_proper_insts:           1008
% 3.36/1.00  inst_num_of_duplicates:                 0
% 3.36/1.00  inst_inst_num_from_inst_to_res:         0
% 3.36/1.00  inst_dismatching_checking_time:         0.
% 3.36/1.00  
% 3.36/1.00  ------ Resolution
% 3.36/1.00  
% 3.36/1.00  res_num_of_clauses:                     0
% 3.36/1.00  res_num_in_passive:                     0
% 3.36/1.00  res_num_in_active:                      0
% 3.36/1.00  res_num_of_loops:                       162
% 3.36/1.00  res_forward_subset_subsumed:            25
% 3.36/1.00  res_backward_subset_subsumed:           0
% 3.36/1.00  res_forward_subsumed:                   0
% 3.36/1.00  res_backward_subsumed:                  0
% 3.36/1.00  res_forward_subsumption_resolution:     0
% 3.36/1.00  res_backward_subsumption_resolution:    0
% 3.36/1.00  res_clause_to_clause_subsumption:       450
% 3.36/1.00  res_orphan_elimination:                 0
% 3.36/1.00  res_tautology_del:                      84
% 3.36/1.00  res_num_eq_res_simplified:              1
% 3.36/1.00  res_num_sel_changes:                    0
% 3.36/1.00  res_moves_from_active_to_pass:          0
% 3.36/1.00  
% 3.36/1.00  ------ Superposition
% 3.36/1.00  
% 3.36/1.00  sup_time_total:                         0.
% 3.36/1.00  sup_time_generating:                    0.
% 3.36/1.00  sup_time_sim_full:                      0.
% 3.36/1.00  sup_time_sim_immed:                     0.
% 3.36/1.00  
% 3.36/1.00  sup_num_of_clauses:                     137
% 3.36/1.00  sup_num_in_active:                      119
% 3.36/1.00  sup_num_in_passive:                     18
% 3.36/1.00  sup_num_of_loops:                       129
% 3.36/1.00  sup_fw_superposition:                   136
% 3.36/1.00  sup_bw_superposition:                   61
% 3.36/1.00  sup_immediate_simplified:               48
% 3.36/1.00  sup_given_eliminated:                   0
% 3.36/1.00  comparisons_done:                       0
% 3.36/1.00  comparisons_avoided:                    3
% 3.36/1.00  
% 3.36/1.00  ------ Simplifications
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  sim_fw_subset_subsumed:                 12
% 3.36/1.00  sim_bw_subset_subsumed:                 4
% 3.36/1.00  sim_fw_subsumed:                        12
% 3.36/1.00  sim_bw_subsumed:                        1
% 3.36/1.00  sim_fw_subsumption_res:                 2
% 3.36/1.00  sim_bw_subsumption_res:                 0
% 3.36/1.00  sim_tautology_del:                      6
% 3.36/1.00  sim_eq_tautology_del:                   9
% 3.36/1.00  sim_eq_res_simp:                        0
% 3.36/1.00  sim_fw_demodulated:                     9
% 3.36/1.00  sim_bw_demodulated:                     10
% 3.36/1.00  sim_light_normalised:                   25
% 3.36/1.00  sim_joinable_taut:                      0
% 3.36/1.00  sim_joinable_simp:                      0
% 3.36/1.00  sim_ac_normalised:                      0
% 3.36/1.00  sim_smt_subsumption:                    0
% 3.36/1.00  
%------------------------------------------------------------------------------
