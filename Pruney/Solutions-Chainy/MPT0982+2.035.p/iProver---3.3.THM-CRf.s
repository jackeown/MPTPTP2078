%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:44 EST 2020

% Result     : Theorem 31.43s
% Output     : CNFRefutation 31.43s
% Verified   : 
% Statistics : Number of formulae       :  198 (1011 expanded)
%              Number of clauses        :  118 ( 380 expanded)
%              Number of leaves         :   21 ( 224 expanded)
%              Depth                    :   18
%              Number of atoms          :  533 (5621 expanded)
%              Number of equality atoms :  251 (1821 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f50,f49])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(nnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1454,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1457,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2288,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1454,c_1457])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2987,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2288,c_1460])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4551,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2987,c_41])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1465,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4555,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4551,c_1465])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1467,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4739,plain,
    ( k3_xboole_0(k2_relat_1(sK4),sK2) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4555,c_1467])).

cnf(c_1873,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1465])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_260,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_321,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_260])).

cnf(c_1450,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_6233,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1873,c_1450])).

cnf(c_1796,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_2698,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_2699,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2698])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2746,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2747,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_6356,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6233,c_1873,c_2699,c_2747])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1461,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6360,plain,
    ( k10_relat_1(sK4,k3_xboole_0(k2_relat_1(sK4),X0)) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_6356,c_1461])).

cnf(c_7158,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k10_relat_1(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_4739,c_6360])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1452,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2289,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1452,c_1457])).

cnf(c_2985,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_1460])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3392,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2985,c_38])).

cnf(c_3396,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3392,c_1465])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1458,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2825,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1454,c_1458])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_556,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_30,c_27])).

cnf(c_2827,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2825,c_556])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_454,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_459,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_32])).

cnf(c_1448,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_3165,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2827,c_1448])).

cnf(c_4558,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3165,c_1873,c_2699,c_2747])).

cnf(c_4559,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4558])).

cnf(c_4565,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3396,c_4559])).

cnf(c_1874,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1465])).

cnf(c_6234,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1450])).

cnf(c_4029,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_4030,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4029])).

cnf(c_4514,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4515,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4514])).

cnf(c_6459,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6234,c_1874,c_4030,c_4515])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1462,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6465,plain,
    ( k9_relat_1(X0,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6459,c_1462])).

cnf(c_8673,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_6356,c_6465])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1459,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2811,plain,
    ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1457])).

cnf(c_5334,plain,
    ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_2811])).

cnf(c_5567,plain,
    ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1452,c_5334])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1456,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3451,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1456])).

cnf(c_3682,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1452,c_3451])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1455,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3470,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1455])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3994,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3470,c_39])).

cnf(c_3995,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3994])).

cnf(c_4004,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_3995])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4263,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4004,c_36])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4265,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4263,c_29])).

cnf(c_5572,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5567,c_3682,c_4265])).

cnf(c_8675,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8673,c_5572])).

cnf(c_17079,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4565,c_4565,c_8675])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_1449,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2128,plain,
    ( k7_relat_1(sK4,sK1) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1449])).

cnf(c_6363,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_6356,c_2128])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1463,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6361,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_6356,c_1463])).

cnf(c_6977,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_6363,c_6361])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1468,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1983,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1448])).

cnf(c_3164,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2827,c_1983])).

cnf(c_3233,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_1873,c_2699,c_2747])).

cnf(c_93947,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6977,c_3233])).

cnf(c_97696,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7158,c_17079,c_93947])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2431,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_2289,c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_97696,c_2431])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.43/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.43/4.50  
% 31.43/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.43/4.50  
% 31.43/4.50  ------  iProver source info
% 31.43/4.50  
% 31.43/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.43/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.43/4.50  git: non_committed_changes: false
% 31.43/4.50  git: last_make_outside_of_git: false
% 31.43/4.50  
% 31.43/4.50  ------ 
% 31.43/4.50  
% 31.43/4.50  ------ Input Options
% 31.43/4.50  
% 31.43/4.50  --out_options                           all
% 31.43/4.50  --tptp_safe_out                         true
% 31.43/4.50  --problem_path                          ""
% 31.43/4.50  --include_path                          ""
% 31.43/4.50  --clausifier                            res/vclausify_rel
% 31.43/4.50  --clausifier_options                    ""
% 31.43/4.50  --stdin                                 false
% 31.43/4.50  --stats_out                             all
% 31.43/4.50  
% 31.43/4.50  ------ General Options
% 31.43/4.50  
% 31.43/4.50  --fof                                   false
% 31.43/4.50  --time_out_real                         305.
% 31.43/4.50  --time_out_virtual                      -1.
% 31.43/4.50  --symbol_type_check                     false
% 31.43/4.50  --clausify_out                          false
% 31.43/4.50  --sig_cnt_out                           false
% 31.43/4.50  --trig_cnt_out                          false
% 31.43/4.50  --trig_cnt_out_tolerance                1.
% 31.43/4.50  --trig_cnt_out_sk_spl                   false
% 31.43/4.50  --abstr_cl_out                          false
% 31.43/4.50  
% 31.43/4.50  ------ Global Options
% 31.43/4.50  
% 31.43/4.50  --schedule                              default
% 31.43/4.50  --add_important_lit                     false
% 31.43/4.50  --prop_solver_per_cl                    1000
% 31.43/4.50  --min_unsat_core                        false
% 31.43/4.50  --soft_assumptions                      false
% 31.43/4.50  --soft_lemma_size                       3
% 31.43/4.50  --prop_impl_unit_size                   0
% 31.43/4.50  --prop_impl_unit                        []
% 31.43/4.50  --share_sel_clauses                     true
% 31.43/4.50  --reset_solvers                         false
% 31.43/4.50  --bc_imp_inh                            [conj_cone]
% 31.43/4.50  --conj_cone_tolerance                   3.
% 31.43/4.50  --extra_neg_conj                        none
% 31.43/4.50  --large_theory_mode                     true
% 31.43/4.50  --prolific_symb_bound                   200
% 31.43/4.50  --lt_threshold                          2000
% 31.43/4.50  --clause_weak_htbl                      true
% 31.43/4.50  --gc_record_bc_elim                     false
% 31.43/4.50  
% 31.43/4.50  ------ Preprocessing Options
% 31.43/4.50  
% 31.43/4.50  --preprocessing_flag                    true
% 31.43/4.50  --time_out_prep_mult                    0.1
% 31.43/4.50  --splitting_mode                        input
% 31.43/4.50  --splitting_grd                         true
% 31.43/4.50  --splitting_cvd                         false
% 31.43/4.50  --splitting_cvd_svl                     false
% 31.43/4.50  --splitting_nvd                         32
% 31.43/4.50  --sub_typing                            true
% 31.43/4.50  --prep_gs_sim                           true
% 31.43/4.50  --prep_unflatten                        true
% 31.43/4.50  --prep_res_sim                          true
% 31.43/4.50  --prep_upred                            true
% 31.43/4.50  --prep_sem_filter                       exhaustive
% 31.43/4.50  --prep_sem_filter_out                   false
% 31.43/4.50  --pred_elim                             true
% 31.43/4.50  --res_sim_input                         true
% 31.43/4.50  --eq_ax_congr_red                       true
% 31.43/4.50  --pure_diseq_elim                       true
% 31.43/4.50  --brand_transform                       false
% 31.43/4.50  --non_eq_to_eq                          false
% 31.43/4.50  --prep_def_merge                        true
% 31.43/4.50  --prep_def_merge_prop_impl              false
% 31.43/4.50  --prep_def_merge_mbd                    true
% 31.43/4.50  --prep_def_merge_tr_red                 false
% 31.43/4.50  --prep_def_merge_tr_cl                  false
% 31.43/4.50  --smt_preprocessing                     true
% 31.43/4.50  --smt_ac_axioms                         fast
% 31.43/4.50  --preprocessed_out                      false
% 31.43/4.50  --preprocessed_stats                    false
% 31.43/4.50  
% 31.43/4.50  ------ Abstraction refinement Options
% 31.43/4.50  
% 31.43/4.50  --abstr_ref                             []
% 31.43/4.50  --abstr_ref_prep                        false
% 31.43/4.50  --abstr_ref_until_sat                   false
% 31.43/4.50  --abstr_ref_sig_restrict                funpre
% 31.43/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.43/4.50  --abstr_ref_under                       []
% 31.43/4.50  
% 31.43/4.50  ------ SAT Options
% 31.43/4.50  
% 31.43/4.50  --sat_mode                              false
% 31.43/4.50  --sat_fm_restart_options                ""
% 31.43/4.50  --sat_gr_def                            false
% 31.43/4.50  --sat_epr_types                         true
% 31.43/4.50  --sat_non_cyclic_types                  false
% 31.43/4.50  --sat_finite_models                     false
% 31.43/4.50  --sat_fm_lemmas                         false
% 31.43/4.50  --sat_fm_prep                           false
% 31.43/4.50  --sat_fm_uc_incr                        true
% 31.43/4.50  --sat_out_model                         small
% 31.43/4.50  --sat_out_clauses                       false
% 31.43/4.50  
% 31.43/4.50  ------ QBF Options
% 31.43/4.50  
% 31.43/4.50  --qbf_mode                              false
% 31.43/4.50  --qbf_elim_univ                         false
% 31.43/4.50  --qbf_dom_inst                          none
% 31.43/4.50  --qbf_dom_pre_inst                      false
% 31.43/4.50  --qbf_sk_in                             false
% 31.43/4.50  --qbf_pred_elim                         true
% 31.43/4.50  --qbf_split                             512
% 31.43/4.50  
% 31.43/4.50  ------ BMC1 Options
% 31.43/4.50  
% 31.43/4.50  --bmc1_incremental                      false
% 31.43/4.50  --bmc1_axioms                           reachable_all
% 31.43/4.50  --bmc1_min_bound                        0
% 31.43/4.50  --bmc1_max_bound                        -1
% 31.43/4.50  --bmc1_max_bound_default                -1
% 31.43/4.50  --bmc1_symbol_reachability              true
% 31.43/4.50  --bmc1_property_lemmas                  false
% 31.43/4.50  --bmc1_k_induction                      false
% 31.43/4.50  --bmc1_non_equiv_states                 false
% 31.43/4.50  --bmc1_deadlock                         false
% 31.43/4.50  --bmc1_ucm                              false
% 31.43/4.50  --bmc1_add_unsat_core                   none
% 31.43/4.50  --bmc1_unsat_core_children              false
% 31.43/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.43/4.50  --bmc1_out_stat                         full
% 31.43/4.50  --bmc1_ground_init                      false
% 31.43/4.50  --bmc1_pre_inst_next_state              false
% 31.43/4.50  --bmc1_pre_inst_state                   false
% 31.43/4.50  --bmc1_pre_inst_reach_state             false
% 31.43/4.50  --bmc1_out_unsat_core                   false
% 31.43/4.50  --bmc1_aig_witness_out                  false
% 31.43/4.50  --bmc1_verbose                          false
% 31.43/4.50  --bmc1_dump_clauses_tptp                false
% 31.43/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.43/4.50  --bmc1_dump_file                        -
% 31.43/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.43/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.43/4.50  --bmc1_ucm_extend_mode                  1
% 31.43/4.50  --bmc1_ucm_init_mode                    2
% 31.43/4.50  --bmc1_ucm_cone_mode                    none
% 31.43/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.43/4.50  --bmc1_ucm_relax_model                  4
% 31.43/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.43/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.43/4.50  --bmc1_ucm_layered_model                none
% 31.43/4.50  --bmc1_ucm_max_lemma_size               10
% 31.43/4.50  
% 31.43/4.50  ------ AIG Options
% 31.43/4.50  
% 31.43/4.50  --aig_mode                              false
% 31.43/4.50  
% 31.43/4.50  ------ Instantiation Options
% 31.43/4.50  
% 31.43/4.50  --instantiation_flag                    true
% 31.43/4.50  --inst_sos_flag                         true
% 31.43/4.50  --inst_sos_phase                        true
% 31.43/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.43/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.43/4.50  --inst_lit_sel_side                     num_symb
% 31.43/4.50  --inst_solver_per_active                1400
% 31.43/4.50  --inst_solver_calls_frac                1.
% 31.43/4.50  --inst_passive_queue_type               priority_queues
% 31.43/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.43/4.50  --inst_passive_queues_freq              [25;2]
% 31.43/4.50  --inst_dismatching                      true
% 31.43/4.50  --inst_eager_unprocessed_to_passive     true
% 31.43/4.50  --inst_prop_sim_given                   true
% 31.43/4.50  --inst_prop_sim_new                     false
% 31.43/4.50  --inst_subs_new                         false
% 31.43/4.50  --inst_eq_res_simp                      false
% 31.43/4.50  --inst_subs_given                       false
% 31.43/4.50  --inst_orphan_elimination               true
% 31.43/4.50  --inst_learning_loop_flag               true
% 31.43/4.50  --inst_learning_start                   3000
% 31.43/4.50  --inst_learning_factor                  2
% 31.43/4.50  --inst_start_prop_sim_after_learn       3
% 31.43/4.50  --inst_sel_renew                        solver
% 31.43/4.50  --inst_lit_activity_flag                true
% 31.43/4.50  --inst_restr_to_given                   false
% 31.43/4.50  --inst_activity_threshold               500
% 31.43/4.50  --inst_out_proof                        true
% 31.43/4.50  
% 31.43/4.50  ------ Resolution Options
% 31.43/4.50  
% 31.43/4.50  --resolution_flag                       true
% 31.43/4.50  --res_lit_sel                           adaptive
% 31.43/4.50  --res_lit_sel_side                      none
% 31.43/4.50  --res_ordering                          kbo
% 31.43/4.50  --res_to_prop_solver                    active
% 31.43/4.50  --res_prop_simpl_new                    false
% 31.43/4.50  --res_prop_simpl_given                  true
% 31.43/4.50  --res_passive_queue_type                priority_queues
% 31.43/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.43/4.51  --res_passive_queues_freq               [15;5]
% 31.43/4.51  --res_forward_subs                      full
% 31.43/4.51  --res_backward_subs                     full
% 31.43/4.51  --res_forward_subs_resolution           true
% 31.43/4.51  --res_backward_subs_resolution          true
% 31.43/4.51  --res_orphan_elimination                true
% 31.43/4.51  --res_time_limit                        2.
% 31.43/4.51  --res_out_proof                         true
% 31.43/4.51  
% 31.43/4.51  ------ Superposition Options
% 31.43/4.51  
% 31.43/4.51  --superposition_flag                    true
% 31.43/4.51  --sup_passive_queue_type                priority_queues
% 31.43/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.43/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.43/4.51  --demod_completeness_check              fast
% 31.43/4.51  --demod_use_ground                      true
% 31.43/4.51  --sup_to_prop_solver                    passive
% 31.43/4.51  --sup_prop_simpl_new                    true
% 31.43/4.51  --sup_prop_simpl_given                  true
% 31.43/4.51  --sup_fun_splitting                     true
% 31.43/4.51  --sup_smt_interval                      50000
% 31.43/4.51  
% 31.43/4.51  ------ Superposition Simplification Setup
% 31.43/4.51  
% 31.43/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.43/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.43/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.43/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.43/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.43/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.43/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.43/4.51  --sup_immed_triv                        [TrivRules]
% 31.43/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_immed_bw_main                     []
% 31.43/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.43/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.43/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_input_bw                          []
% 31.43/4.51  
% 31.43/4.51  ------ Combination Options
% 31.43/4.51  
% 31.43/4.51  --comb_res_mult                         3
% 31.43/4.51  --comb_sup_mult                         2
% 31.43/4.51  --comb_inst_mult                        10
% 31.43/4.51  
% 31.43/4.51  ------ Debug Options
% 31.43/4.51  
% 31.43/4.51  --dbg_backtrace                         false
% 31.43/4.51  --dbg_dump_prop_clauses                 false
% 31.43/4.51  --dbg_dump_prop_clauses_file            -
% 31.43/4.51  --dbg_out_stat                          false
% 31.43/4.51  ------ Parsing...
% 31.43/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.43/4.51  
% 31.43/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.43/4.51  
% 31.43/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.43/4.51  
% 31.43/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.43/4.51  ------ Proving...
% 31.43/4.51  ------ Problem Properties 
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  clauses                                 31
% 31.43/4.51  conjectures                             7
% 31.43/4.51  EPR                                     6
% 31.43/4.51  Horn                                    28
% 31.43/4.51  unary                                   10
% 31.43/4.51  binary                                  9
% 31.43/4.51  lits                                    68
% 31.43/4.51  lits eq                                 27
% 31.43/4.51  fd_pure                                 0
% 31.43/4.51  fd_pseudo                               0
% 31.43/4.51  fd_cond                                 0
% 31.43/4.51  fd_pseudo_cond                          1
% 31.43/4.51  AC symbols                              0
% 31.43/4.51  
% 31.43/4.51  ------ Schedule dynamic 5 is on 
% 31.43/4.51  
% 31.43/4.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  ------ 
% 31.43/4.51  Current options:
% 31.43/4.51  ------ 
% 31.43/4.51  
% 31.43/4.51  ------ Input Options
% 31.43/4.51  
% 31.43/4.51  --out_options                           all
% 31.43/4.51  --tptp_safe_out                         true
% 31.43/4.51  --problem_path                          ""
% 31.43/4.51  --include_path                          ""
% 31.43/4.51  --clausifier                            res/vclausify_rel
% 31.43/4.51  --clausifier_options                    ""
% 31.43/4.51  --stdin                                 false
% 31.43/4.51  --stats_out                             all
% 31.43/4.51  
% 31.43/4.51  ------ General Options
% 31.43/4.51  
% 31.43/4.51  --fof                                   false
% 31.43/4.51  --time_out_real                         305.
% 31.43/4.51  --time_out_virtual                      -1.
% 31.43/4.51  --symbol_type_check                     false
% 31.43/4.51  --clausify_out                          false
% 31.43/4.51  --sig_cnt_out                           false
% 31.43/4.51  --trig_cnt_out                          false
% 31.43/4.51  --trig_cnt_out_tolerance                1.
% 31.43/4.51  --trig_cnt_out_sk_spl                   false
% 31.43/4.51  --abstr_cl_out                          false
% 31.43/4.51  
% 31.43/4.51  ------ Global Options
% 31.43/4.51  
% 31.43/4.51  --schedule                              default
% 31.43/4.51  --add_important_lit                     false
% 31.43/4.51  --prop_solver_per_cl                    1000
% 31.43/4.51  --min_unsat_core                        false
% 31.43/4.51  --soft_assumptions                      false
% 31.43/4.51  --soft_lemma_size                       3
% 31.43/4.51  --prop_impl_unit_size                   0
% 31.43/4.51  --prop_impl_unit                        []
% 31.43/4.51  --share_sel_clauses                     true
% 31.43/4.51  --reset_solvers                         false
% 31.43/4.51  --bc_imp_inh                            [conj_cone]
% 31.43/4.51  --conj_cone_tolerance                   3.
% 31.43/4.51  --extra_neg_conj                        none
% 31.43/4.51  --large_theory_mode                     true
% 31.43/4.51  --prolific_symb_bound                   200
% 31.43/4.51  --lt_threshold                          2000
% 31.43/4.51  --clause_weak_htbl                      true
% 31.43/4.51  --gc_record_bc_elim                     false
% 31.43/4.51  
% 31.43/4.51  ------ Preprocessing Options
% 31.43/4.51  
% 31.43/4.51  --preprocessing_flag                    true
% 31.43/4.51  --time_out_prep_mult                    0.1
% 31.43/4.51  --splitting_mode                        input
% 31.43/4.51  --splitting_grd                         true
% 31.43/4.51  --splitting_cvd                         false
% 31.43/4.51  --splitting_cvd_svl                     false
% 31.43/4.51  --splitting_nvd                         32
% 31.43/4.51  --sub_typing                            true
% 31.43/4.51  --prep_gs_sim                           true
% 31.43/4.51  --prep_unflatten                        true
% 31.43/4.51  --prep_res_sim                          true
% 31.43/4.51  --prep_upred                            true
% 31.43/4.51  --prep_sem_filter                       exhaustive
% 31.43/4.51  --prep_sem_filter_out                   false
% 31.43/4.51  --pred_elim                             true
% 31.43/4.51  --res_sim_input                         true
% 31.43/4.51  --eq_ax_congr_red                       true
% 31.43/4.51  --pure_diseq_elim                       true
% 31.43/4.51  --brand_transform                       false
% 31.43/4.51  --non_eq_to_eq                          false
% 31.43/4.51  --prep_def_merge                        true
% 31.43/4.51  --prep_def_merge_prop_impl              false
% 31.43/4.51  --prep_def_merge_mbd                    true
% 31.43/4.51  --prep_def_merge_tr_red                 false
% 31.43/4.51  --prep_def_merge_tr_cl                  false
% 31.43/4.51  --smt_preprocessing                     true
% 31.43/4.51  --smt_ac_axioms                         fast
% 31.43/4.51  --preprocessed_out                      false
% 31.43/4.51  --preprocessed_stats                    false
% 31.43/4.51  
% 31.43/4.51  ------ Abstraction refinement Options
% 31.43/4.51  
% 31.43/4.51  --abstr_ref                             []
% 31.43/4.51  --abstr_ref_prep                        false
% 31.43/4.51  --abstr_ref_until_sat                   false
% 31.43/4.51  --abstr_ref_sig_restrict                funpre
% 31.43/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.43/4.51  --abstr_ref_under                       []
% 31.43/4.51  
% 31.43/4.51  ------ SAT Options
% 31.43/4.51  
% 31.43/4.51  --sat_mode                              false
% 31.43/4.51  --sat_fm_restart_options                ""
% 31.43/4.51  --sat_gr_def                            false
% 31.43/4.51  --sat_epr_types                         true
% 31.43/4.51  --sat_non_cyclic_types                  false
% 31.43/4.51  --sat_finite_models                     false
% 31.43/4.51  --sat_fm_lemmas                         false
% 31.43/4.51  --sat_fm_prep                           false
% 31.43/4.51  --sat_fm_uc_incr                        true
% 31.43/4.51  --sat_out_model                         small
% 31.43/4.51  --sat_out_clauses                       false
% 31.43/4.51  
% 31.43/4.51  ------ QBF Options
% 31.43/4.51  
% 31.43/4.51  --qbf_mode                              false
% 31.43/4.51  --qbf_elim_univ                         false
% 31.43/4.51  --qbf_dom_inst                          none
% 31.43/4.51  --qbf_dom_pre_inst                      false
% 31.43/4.51  --qbf_sk_in                             false
% 31.43/4.51  --qbf_pred_elim                         true
% 31.43/4.51  --qbf_split                             512
% 31.43/4.51  
% 31.43/4.51  ------ BMC1 Options
% 31.43/4.51  
% 31.43/4.51  --bmc1_incremental                      false
% 31.43/4.51  --bmc1_axioms                           reachable_all
% 31.43/4.51  --bmc1_min_bound                        0
% 31.43/4.51  --bmc1_max_bound                        -1
% 31.43/4.51  --bmc1_max_bound_default                -1
% 31.43/4.51  --bmc1_symbol_reachability              true
% 31.43/4.51  --bmc1_property_lemmas                  false
% 31.43/4.51  --bmc1_k_induction                      false
% 31.43/4.51  --bmc1_non_equiv_states                 false
% 31.43/4.51  --bmc1_deadlock                         false
% 31.43/4.51  --bmc1_ucm                              false
% 31.43/4.51  --bmc1_add_unsat_core                   none
% 31.43/4.51  --bmc1_unsat_core_children              false
% 31.43/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.43/4.51  --bmc1_out_stat                         full
% 31.43/4.51  --bmc1_ground_init                      false
% 31.43/4.51  --bmc1_pre_inst_next_state              false
% 31.43/4.51  --bmc1_pre_inst_state                   false
% 31.43/4.51  --bmc1_pre_inst_reach_state             false
% 31.43/4.51  --bmc1_out_unsat_core                   false
% 31.43/4.51  --bmc1_aig_witness_out                  false
% 31.43/4.51  --bmc1_verbose                          false
% 31.43/4.51  --bmc1_dump_clauses_tptp                false
% 31.43/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.43/4.51  --bmc1_dump_file                        -
% 31.43/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.43/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.43/4.51  --bmc1_ucm_extend_mode                  1
% 31.43/4.51  --bmc1_ucm_init_mode                    2
% 31.43/4.51  --bmc1_ucm_cone_mode                    none
% 31.43/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.43/4.51  --bmc1_ucm_relax_model                  4
% 31.43/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.43/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.43/4.51  --bmc1_ucm_layered_model                none
% 31.43/4.51  --bmc1_ucm_max_lemma_size               10
% 31.43/4.51  
% 31.43/4.51  ------ AIG Options
% 31.43/4.51  
% 31.43/4.51  --aig_mode                              false
% 31.43/4.51  
% 31.43/4.51  ------ Instantiation Options
% 31.43/4.51  
% 31.43/4.51  --instantiation_flag                    true
% 31.43/4.51  --inst_sos_flag                         true
% 31.43/4.51  --inst_sos_phase                        true
% 31.43/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.43/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.43/4.51  --inst_lit_sel_side                     none
% 31.43/4.51  --inst_solver_per_active                1400
% 31.43/4.51  --inst_solver_calls_frac                1.
% 31.43/4.51  --inst_passive_queue_type               priority_queues
% 31.43/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.43/4.51  --inst_passive_queues_freq              [25;2]
% 31.43/4.51  --inst_dismatching                      true
% 31.43/4.51  --inst_eager_unprocessed_to_passive     true
% 31.43/4.51  --inst_prop_sim_given                   true
% 31.43/4.51  --inst_prop_sim_new                     false
% 31.43/4.51  --inst_subs_new                         false
% 31.43/4.51  --inst_eq_res_simp                      false
% 31.43/4.51  --inst_subs_given                       false
% 31.43/4.51  --inst_orphan_elimination               true
% 31.43/4.51  --inst_learning_loop_flag               true
% 31.43/4.51  --inst_learning_start                   3000
% 31.43/4.51  --inst_learning_factor                  2
% 31.43/4.51  --inst_start_prop_sim_after_learn       3
% 31.43/4.51  --inst_sel_renew                        solver
% 31.43/4.51  --inst_lit_activity_flag                true
% 31.43/4.51  --inst_restr_to_given                   false
% 31.43/4.51  --inst_activity_threshold               500
% 31.43/4.51  --inst_out_proof                        true
% 31.43/4.51  
% 31.43/4.51  ------ Resolution Options
% 31.43/4.51  
% 31.43/4.51  --resolution_flag                       false
% 31.43/4.51  --res_lit_sel                           adaptive
% 31.43/4.51  --res_lit_sel_side                      none
% 31.43/4.51  --res_ordering                          kbo
% 31.43/4.51  --res_to_prop_solver                    active
% 31.43/4.51  --res_prop_simpl_new                    false
% 31.43/4.51  --res_prop_simpl_given                  true
% 31.43/4.51  --res_passive_queue_type                priority_queues
% 31.43/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.43/4.51  --res_passive_queues_freq               [15;5]
% 31.43/4.51  --res_forward_subs                      full
% 31.43/4.51  --res_backward_subs                     full
% 31.43/4.51  --res_forward_subs_resolution           true
% 31.43/4.51  --res_backward_subs_resolution          true
% 31.43/4.51  --res_orphan_elimination                true
% 31.43/4.51  --res_time_limit                        2.
% 31.43/4.51  --res_out_proof                         true
% 31.43/4.51  
% 31.43/4.51  ------ Superposition Options
% 31.43/4.51  
% 31.43/4.51  --superposition_flag                    true
% 31.43/4.51  --sup_passive_queue_type                priority_queues
% 31.43/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.43/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.43/4.51  --demod_completeness_check              fast
% 31.43/4.51  --demod_use_ground                      true
% 31.43/4.51  --sup_to_prop_solver                    passive
% 31.43/4.51  --sup_prop_simpl_new                    true
% 31.43/4.51  --sup_prop_simpl_given                  true
% 31.43/4.51  --sup_fun_splitting                     true
% 31.43/4.51  --sup_smt_interval                      50000
% 31.43/4.51  
% 31.43/4.51  ------ Superposition Simplification Setup
% 31.43/4.51  
% 31.43/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.43/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.43/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.43/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.43/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.43/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.43/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.43/4.51  --sup_immed_triv                        [TrivRules]
% 31.43/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_immed_bw_main                     []
% 31.43/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.43/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.43/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.43/4.51  --sup_input_bw                          []
% 31.43/4.51  
% 31.43/4.51  ------ Combination Options
% 31.43/4.51  
% 31.43/4.51  --comb_res_mult                         3
% 31.43/4.51  --comb_sup_mult                         2
% 31.43/4.51  --comb_inst_mult                        10
% 31.43/4.51  
% 31.43/4.51  ------ Debug Options
% 31.43/4.51  
% 31.43/4.51  --dbg_backtrace                         false
% 31.43/4.51  --dbg_dump_prop_clauses                 false
% 31.43/4.51  --dbg_dump_prop_clauses_file            -
% 31.43/4.51  --dbg_out_stat                          false
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  ------ Proving...
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  % SZS status Theorem for theBenchmark.p
% 31.43/4.51  
% 31.43/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.43/4.51  
% 31.43/4.51  fof(f19,conjecture,(
% 31.43/4.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f20,negated_conjecture,(
% 31.43/4.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 31.43/4.51    inference(negated_conjecture,[],[f19])).
% 31.43/4.51  
% 31.43/4.51  fof(f43,plain,(
% 31.43/4.51    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 31.43/4.51    inference(ennf_transformation,[],[f20])).
% 31.43/4.51  
% 31.43/4.51  fof(f44,plain,(
% 31.43/4.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 31.43/4.51    inference(flattening,[],[f43])).
% 31.43/4.51  
% 31.43/4.51  fof(f50,plain,(
% 31.43/4.51    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 31.43/4.51    introduced(choice_axiom,[])).
% 31.43/4.51  
% 31.43/4.51  fof(f49,plain,(
% 31.43/4.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 31.43/4.51    introduced(choice_axiom,[])).
% 31.43/4.51  
% 31.43/4.51  fof(f51,plain,(
% 31.43/4.51    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 31.43/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f50,f49])).
% 31.43/4.51  
% 31.43/4.51  fof(f83,plain,(
% 31.43/4.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f15,axiom,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f36,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(ennf_transformation,[],[f15])).
% 31.43/4.51  
% 31.43/4.51  fof(f69,plain,(
% 31.43/4.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f36])).
% 31.43/4.51  
% 31.43/4.51  fof(f12,axiom,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f32,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(ennf_transformation,[],[f12])).
% 31.43/4.51  
% 31.43/4.51  fof(f66,plain,(
% 31.43/4.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f32])).
% 31.43/4.51  
% 31.43/4.51  fof(f3,axiom,(
% 31.43/4.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f47,plain,(
% 31.43/4.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.43/4.51    inference(nnf_transformation,[],[f3])).
% 31.43/4.51  
% 31.43/4.51  fof(f56,plain,(
% 31.43/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f47])).
% 31.43/4.51  
% 31.43/4.51  fof(f2,axiom,(
% 31.43/4.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f22,plain,(
% 31.43/4.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.43/4.51    inference(ennf_transformation,[],[f2])).
% 31.43/4.51  
% 31.43/4.51  fof(f55,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f22])).
% 31.43/4.51  
% 31.43/4.51  fof(f4,axiom,(
% 31.43/4.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f23,plain,(
% 31.43/4.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.43/4.51    inference(ennf_transformation,[],[f4])).
% 31.43/4.51  
% 31.43/4.51  fof(f58,plain,(
% 31.43/4.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f23])).
% 31.43/4.51  
% 31.43/4.51  fof(f57,plain,(
% 31.43/4.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f47])).
% 31.43/4.51  
% 31.43/4.51  fof(f5,axiom,(
% 31.43/4.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f59,plain,(
% 31.43/4.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f5])).
% 31.43/4.51  
% 31.43/4.51  fof(f8,axiom,(
% 31.43/4.51    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f26,plain,(
% 31.43/4.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.43/4.51    inference(ennf_transformation,[],[f8])).
% 31.43/4.51  
% 31.43/4.51  fof(f62,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f26])).
% 31.43/4.51  
% 31.43/4.51  fof(f80,plain,(
% 31.43/4.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f14,axiom,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f35,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(ennf_transformation,[],[f14])).
% 31.43/4.51  
% 31.43/4.51  fof(f68,plain,(
% 31.43/4.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f35])).
% 31.43/4.51  
% 31.43/4.51  fof(f17,axiom,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f39,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(ennf_transformation,[],[f17])).
% 31.43/4.51  
% 31.43/4.51  fof(f40,plain,(
% 31.43/4.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(flattening,[],[f39])).
% 31.43/4.51  
% 31.43/4.51  fof(f48,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(nnf_transformation,[],[f40])).
% 31.43/4.51  
% 31.43/4.51  fof(f71,plain,(
% 31.43/4.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f48])).
% 31.43/4.51  
% 31.43/4.51  fof(f82,plain,(
% 31.43/4.51    v1_funct_2(sK4,sK1,sK2)),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f86,plain,(
% 31.43/4.51    k1_xboole_0 != sK2),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f10,axiom,(
% 31.43/4.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f29,plain,(
% 31.43/4.51    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 31.43/4.51    inference(ennf_transformation,[],[f10])).
% 31.43/4.51  
% 31.43/4.51  fof(f30,plain,(
% 31.43/4.51    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 31.43/4.51    inference(flattening,[],[f29])).
% 31.43/4.51  
% 31.43/4.51  fof(f64,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f30])).
% 31.43/4.51  
% 31.43/4.51  fof(f85,plain,(
% 31.43/4.51    v2_funct_1(sK4)),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f81,plain,(
% 31.43/4.51    v1_funct_1(sK4)),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f7,axiom,(
% 31.43/4.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f25,plain,(
% 31.43/4.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.43/4.51    inference(ennf_transformation,[],[f7])).
% 31.43/4.51  
% 31.43/4.51  fof(f61,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f25])).
% 31.43/4.51  
% 31.43/4.51  fof(f13,axiom,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f33,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.43/4.51    inference(ennf_transformation,[],[f13])).
% 31.43/4.51  
% 31.43/4.51  fof(f34,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(flattening,[],[f33])).
% 31.43/4.51  
% 31.43/4.51  fof(f67,plain,(
% 31.43/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f34])).
% 31.43/4.51  
% 31.43/4.51  fof(f16,axiom,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f37,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.43/4.51    inference(ennf_transformation,[],[f16])).
% 31.43/4.51  
% 31.43/4.51  fof(f38,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(flattening,[],[f37])).
% 31.43/4.51  
% 31.43/4.51  fof(f70,plain,(
% 31.43/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f38])).
% 31.43/4.51  
% 31.43/4.51  fof(f18,axiom,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f41,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.43/4.51    inference(ennf_transformation,[],[f18])).
% 31.43/4.51  
% 31.43/4.51  fof(f42,plain,(
% 31.43/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.43/4.51    inference(flattening,[],[f41])).
% 31.43/4.51  
% 31.43/4.51  fof(f77,plain,(
% 31.43/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f42])).
% 31.43/4.51  
% 31.43/4.51  fof(f78,plain,(
% 31.43/4.51    v1_funct_1(sK3)),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f84,plain,(
% 31.43/4.51    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  fof(f11,axiom,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f21,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.43/4.51    inference(pure_predicate_removal,[],[f11])).
% 31.43/4.51  
% 31.43/4.51  fof(f31,plain,(
% 31.43/4.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.43/4.51    inference(ennf_transformation,[],[f21])).
% 31.43/4.51  
% 31.43/4.51  fof(f65,plain,(
% 31.43/4.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.43/4.51    inference(cnf_transformation,[],[f31])).
% 31.43/4.51  
% 31.43/4.51  fof(f9,axiom,(
% 31.43/4.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f27,plain,(
% 31.43/4.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.43/4.51    inference(ennf_transformation,[],[f9])).
% 31.43/4.51  
% 31.43/4.51  fof(f28,plain,(
% 31.43/4.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.43/4.51    inference(flattening,[],[f27])).
% 31.43/4.51  
% 31.43/4.51  fof(f63,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f28])).
% 31.43/4.51  
% 31.43/4.51  fof(f6,axiom,(
% 31.43/4.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f24,plain,(
% 31.43/4.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.43/4.51    inference(ennf_transformation,[],[f6])).
% 31.43/4.51  
% 31.43/4.51  fof(f60,plain,(
% 31.43/4.51    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.43/4.51    inference(cnf_transformation,[],[f24])).
% 31.43/4.51  
% 31.43/4.51  fof(f1,axiom,(
% 31.43/4.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.43/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.43/4.51  
% 31.43/4.51  fof(f45,plain,(
% 31.43/4.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.43/4.51    inference(nnf_transformation,[],[f1])).
% 31.43/4.51  
% 31.43/4.51  fof(f46,plain,(
% 31.43/4.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.43/4.51    inference(flattening,[],[f45])).
% 31.43/4.51  
% 31.43/4.51  fof(f53,plain,(
% 31.43/4.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 31.43/4.51    inference(cnf_transformation,[],[f46])).
% 31.43/4.51  
% 31.43/4.51  fof(f88,plain,(
% 31.43/4.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.43/4.51    inference(equality_resolution,[],[f53])).
% 31.43/4.51  
% 31.43/4.51  fof(f87,plain,(
% 31.43/4.51    k2_relset_1(sK0,sK1,sK3) != sK1),
% 31.43/4.51    inference(cnf_transformation,[],[f51])).
% 31.43/4.51  
% 31.43/4.51  cnf(c_30,negated_conjecture,
% 31.43/4.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 31.43/4.51      inference(cnf_transformation,[],[f83]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1454,plain,
% 31.43/4.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_17,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f69]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1457,plain,
% 31.43/4.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2288,plain,
% 31.43/4.51      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1457]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_14,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 31.43/4.51      inference(cnf_transformation,[],[f66]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1460,plain,
% 31.43/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.43/4.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2987,plain,
% 31.43/4.51      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 31.43/4.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_2288,c_1460]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_41,plain,
% 31.43/4.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4551,plain,
% 31.43/4.51      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_2987,c_41]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_5,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.43/4.51      inference(cnf_transformation,[],[f56]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1465,plain,
% 31.43/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.43/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4555,plain,
% 31.43/4.51      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_4551,c_1465]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.43/4.51      inference(cnf_transformation,[],[f55]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1467,plain,
% 31.43/4.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4739,plain,
% 31.43/4.51      ( k3_xboole_0(k2_relat_1(sK4),sK2) = k2_relat_1(sK4) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_4555,c_1467]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1873,plain,
% 31.43/4.51      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1465]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.43/4.51      | ~ v1_relat_1(X1)
% 31.43/4.51      | v1_relat_1(X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f58]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4,plain,
% 31.43/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.43/4.51      inference(cnf_transformation,[],[f57]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_259,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.43/4.51      inference(prop_impl,[status(thm)],[c_4]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_260,plain,
% 31.43/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.43/4.51      inference(renaming,[status(thm)],[c_259]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_321,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.43/4.51      inference(bin_hyper_res,[status(thm)],[c_6,c_260]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1450,plain,
% 31.43/4.51      ( r1_tarski(X0,X1) != iProver_top
% 31.43/4.51      | v1_relat_1(X1) != iProver_top
% 31.43/4.51      | v1_relat_1(X0) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6233,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 31.43/4.51      | v1_relat_1(sK4) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1873,c_1450]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1796,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 31.43/4.51      | v1_relat_1(X0)
% 31.43/4.51      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 31.43/4.51      inference(instantiation,[status(thm)],[c_321]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2698,plain,
% 31.43/4.51      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 31.43/4.51      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 31.43/4.51      | v1_relat_1(sK4) ),
% 31.43/4.51      inference(instantiation,[status(thm)],[c_1796]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2699,plain,
% 31.43/4.51      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 31.43/4.51      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 31.43/4.51      | v1_relat_1(sK4) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_2698]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_7,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.43/4.51      inference(cnf_transformation,[],[f59]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2746,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 31.43/4.51      inference(instantiation,[status(thm)],[c_7]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2747,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6356,plain,
% 31.43/4.51      ( v1_relat_1(sK4) = iProver_top ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_6233,c_1873,c_2699,c_2747]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_10,plain,
% 31.43/4.51      ( ~ v1_relat_1(X0)
% 31.43/4.51      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 31.43/4.51      inference(cnf_transformation,[],[f62]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1461,plain,
% 31.43/4.51      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 31.43/4.51      | v1_relat_1(X0) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6360,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k3_xboole_0(k2_relat_1(sK4),X0)) = k10_relat_1(sK4,X0) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6356,c_1461]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_7158,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k10_relat_1(sK4,sK2) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_4739,c_6360]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_33,negated_conjecture,
% 31.43/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.43/4.51      inference(cnf_transformation,[],[f80]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1452,plain,
% 31.43/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2289,plain,
% 31.43/4.51      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1452,c_1457]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2985,plain,
% 31.43/4.51      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 31.43/4.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_2289,c_1460]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_38,plain,
% 31.43/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3392,plain,
% 31.43/4.51      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_2985,c_38]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3396,plain,
% 31.43/4.51      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_3392,c_1465]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_16,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f68]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1458,plain,
% 31.43/4.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2825,plain,
% 31.43/4.51      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1458]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_24,plain,
% 31.43/4.51      ( ~ v1_funct_2(X0,X1,X2)
% 31.43/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | k1_relset_1(X1,X2,X0) = X1
% 31.43/4.51      | k1_xboole_0 = X2 ),
% 31.43/4.51      inference(cnf_transformation,[],[f71]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_31,negated_conjecture,
% 31.43/4.51      ( v1_funct_2(sK4,sK1,sK2) ),
% 31.43/4.51      inference(cnf_transformation,[],[f82]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_553,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | k1_relset_1(X1,X2,X0) = X1
% 31.43/4.51      | sK4 != X0
% 31.43/4.51      | sK2 != X2
% 31.43/4.51      | sK1 != X1
% 31.43/4.51      | k1_xboole_0 = X2 ),
% 31.43/4.51      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_554,plain,
% 31.43/4.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 31.43/4.51      | k1_relset_1(sK1,sK2,sK4) = sK1
% 31.43/4.51      | k1_xboole_0 = sK2 ),
% 31.43/4.51      inference(unflattening,[status(thm)],[c_553]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_27,negated_conjecture,
% 31.43/4.51      ( k1_xboole_0 != sK2 ),
% 31.43/4.51      inference(cnf_transformation,[],[f86]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_556,plain,
% 31.43/4.51      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_554,c_30,c_27]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2827,plain,
% 31.43/4.51      ( k1_relat_1(sK4) = sK1 ),
% 31.43/4.51      inference(light_normalisation,[status(thm)],[c_2825,c_556]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_12,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 31.43/4.51      | ~ v1_funct_1(X1)
% 31.43/4.51      | ~ v2_funct_1(X1)
% 31.43/4.51      | ~ v1_relat_1(X1)
% 31.43/4.51      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 31.43/4.51      inference(cnf_transformation,[],[f64]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_28,negated_conjecture,
% 31.43/4.51      ( v2_funct_1(sK4) ),
% 31.43/4.51      inference(cnf_transformation,[],[f85]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_454,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 31.43/4.51      | ~ v1_funct_1(X1)
% 31.43/4.51      | ~ v1_relat_1(X1)
% 31.43/4.51      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 31.43/4.51      | sK4 != X1 ),
% 31.43/4.51      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_455,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 31.43/4.51      | ~ v1_funct_1(sK4)
% 31.43/4.51      | ~ v1_relat_1(sK4)
% 31.43/4.51      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 31.43/4.51      inference(unflattening,[status(thm)],[c_454]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_32,negated_conjecture,
% 31.43/4.51      ( v1_funct_1(sK4) ),
% 31.43/4.51      inference(cnf_transformation,[],[f81]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_459,plain,
% 31.43/4.51      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 31.43/4.51      | ~ v1_relat_1(sK4)
% 31.43/4.51      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_455,c_32]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1448,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 31.43/4.51      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 31.43/4.51      | v1_relat_1(sK4) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3165,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 31.43/4.51      | r1_tarski(X0,sK1) != iProver_top
% 31.43/4.51      | v1_relat_1(sK4) != iProver_top ),
% 31.43/4.51      inference(demodulation,[status(thm)],[c_2827,c_1448]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4558,plain,
% 31.43/4.51      ( r1_tarski(X0,sK1) != iProver_top
% 31.43/4.51      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_3165,c_1873,c_2699,c_2747]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4559,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 31.43/4.51      | r1_tarski(X0,sK1) != iProver_top ),
% 31.43/4.51      inference(renaming,[status(thm)],[c_4558]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4565,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_3396,c_4559]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1874,plain,
% 31.43/4.51      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1452,c_1465]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6234,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.43/4.51      | v1_relat_1(sK3) = iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1874,c_1450]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4029,plain,
% 31.43/4.51      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 31.43/4.51      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 31.43/4.51      | v1_relat_1(sK3) ),
% 31.43/4.51      inference(instantiation,[status(thm)],[c_1796]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4030,plain,
% 31.43/4.51      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.43/4.51      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.43/4.51      | v1_relat_1(sK3) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_4029]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4514,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.43/4.51      inference(instantiation,[status(thm)],[c_7]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4515,plain,
% 31.43/4.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_4514]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6459,plain,
% 31.43/4.51      ( v1_relat_1(sK3) = iProver_top ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_6234,c_1874,c_4030,c_4515]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_9,plain,
% 31.43/4.51      ( ~ v1_relat_1(X0)
% 31.43/4.51      | ~ v1_relat_1(X1)
% 31.43/4.51      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 31.43/4.51      inference(cnf_transformation,[],[f61]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1462,plain,
% 31.43/4.51      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 31.43/4.51      | v1_relat_1(X0) != iProver_top
% 31.43/4.51      | v1_relat_1(X1) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6465,plain,
% 31.43/4.51      ( k9_relat_1(X0,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,X0))
% 31.43/4.51      | v1_relat_1(X0) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6459,c_1462]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_8673,plain,
% 31.43/4.51      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6356,c_6465]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_15,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.43/4.51      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 31.43/4.51      inference(cnf_transformation,[],[f67]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1459,plain,
% 31.43/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.43/4.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.43/4.51      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2811,plain,
% 31.43/4.51      ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
% 31.43/4.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 31.43/4.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1459,c_1457]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_5334,plain,
% 31.43/4.51      ( k2_relset_1(X0,sK2,k4_relset_1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4))
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_2811]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_5567,plain,
% 31.43/4.51      ( k2_relset_1(sK0,sK2,k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1452,c_5334]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_18,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.43/4.51      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f70]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1456,plain,
% 31.43/4.51      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.43/4.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.43/4.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3451,plain,
% 31.43/4.51      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1456]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3682,plain,
% 31.43/4.51      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1452,c_3451]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_25,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.43/4.51      | ~ v1_funct_1(X0)
% 31.43/4.51      | ~ v1_funct_1(X3)
% 31.43/4.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f77]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1455,plain,
% 31.43/4.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.43/4.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.43/4.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.43/4.51      | v1_funct_1(X5) != iProver_top
% 31.43/4.51      | v1_funct_1(X4) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3470,plain,
% 31.43/4.51      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.43/4.51      | v1_funct_1(X2) != iProver_top
% 31.43/4.51      | v1_funct_1(sK4) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1455]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_39,plain,
% 31.43/4.51      ( v1_funct_1(sK4) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3994,plain,
% 31.43/4.51      ( v1_funct_1(X2) != iProver_top
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.43/4.51      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_3470,c_39]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3995,plain,
% 31.43/4.51      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 31.43/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.43/4.51      | v1_funct_1(X2) != iProver_top ),
% 31.43/4.51      inference(renaming,[status(thm)],[c_3994]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4004,plain,
% 31.43/4.51      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 31.43/4.51      | v1_funct_1(sK3) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1452,c_3995]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_35,negated_conjecture,
% 31.43/4.51      ( v1_funct_1(sK3) ),
% 31.43/4.51      inference(cnf_transformation,[],[f78]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_36,plain,
% 31.43/4.51      ( v1_funct_1(sK3) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4263,plain,
% 31.43/4.51      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_4004,c_36]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_29,negated_conjecture,
% 31.43/4.51      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 31.43/4.51      inference(cnf_transformation,[],[f84]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_4265,plain,
% 31.43/4.51      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 31.43/4.51      inference(demodulation,[status(thm)],[c_4263,c_29]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_5572,plain,
% 31.43/4.51      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 31.43/4.51      inference(light_normalisation,[status(thm)],[c_5567,c_3682,c_4265]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_8675,plain,
% 31.43/4.51      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 31.43/4.51      inference(light_normalisation,[status(thm)],[c_8673,c_5572]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_17079,plain,
% 31.43/4.51      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 31.43/4.51      inference(light_normalisation,[status(thm)],[c_4565,c_4565,c_8675]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_13,plain,
% 31.43/4.51      ( v4_relat_1(X0,X1)
% 31.43/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.43/4.51      inference(cnf_transformation,[],[f65]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_11,plain,
% 31.43/4.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 31.43/4.51      inference(cnf_transformation,[],[f63]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_436,plain,
% 31.43/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.43/4.51      | ~ v1_relat_1(X0)
% 31.43/4.51      | k7_relat_1(X0,X1) = X0 ),
% 31.43/4.51      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1449,plain,
% 31.43/4.51      ( k7_relat_1(X0,X1) = X0
% 31.43/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.43/4.51      | v1_relat_1(X0) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2128,plain,
% 31.43/4.51      ( k7_relat_1(sK4,sK1) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1454,c_1449]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6363,plain,
% 31.43/4.51      ( k7_relat_1(sK4,sK1) = sK4 ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6356,c_2128]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_8,plain,
% 31.43/4.51      ( ~ v1_relat_1(X0)
% 31.43/4.51      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 31.43/4.51      inference(cnf_transformation,[],[f60]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1463,plain,
% 31.43/4.51      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 31.43/4.51      | v1_relat_1(X0) != iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6361,plain,
% 31.43/4.51      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6356,c_1463]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_6977,plain,
% 31.43/4.51      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_6363,c_6361]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1,plain,
% 31.43/4.51      ( r1_tarski(X0,X0) ),
% 31.43/4.51      inference(cnf_transformation,[],[f88]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1468,plain,
% 31.43/4.51      ( r1_tarski(X0,X0) = iProver_top ),
% 31.43/4.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_1983,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4)
% 31.43/4.51      | v1_relat_1(sK4) != iProver_top ),
% 31.43/4.51      inference(superposition,[status(thm)],[c_1468,c_1448]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3164,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1
% 31.43/4.51      | v1_relat_1(sK4) != iProver_top ),
% 31.43/4.51      inference(demodulation,[status(thm)],[c_2827,c_1983]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_3233,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k9_relat_1(sK4,sK1)) = sK1 ),
% 31.43/4.51      inference(global_propositional_subsumption,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_3164,c_1873,c_2699,c_2747]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_93947,plain,
% 31.43/4.51      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 31.43/4.51      inference(demodulation,[status(thm)],[c_6977,c_3233]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_97696,plain,
% 31.43/4.51      ( k2_relat_1(sK3) = sK1 ),
% 31.43/4.51      inference(light_normalisation,
% 31.43/4.51                [status(thm)],
% 31.43/4.51                [c_7158,c_17079,c_93947]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_26,negated_conjecture,
% 31.43/4.51      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 31.43/4.51      inference(cnf_transformation,[],[f87]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(c_2431,plain,
% 31.43/4.51      ( k2_relat_1(sK3) != sK1 ),
% 31.43/4.51      inference(demodulation,[status(thm)],[c_2289,c_26]) ).
% 31.43/4.51  
% 31.43/4.51  cnf(contradiction,plain,
% 31.43/4.51      ( $false ),
% 31.43/4.51      inference(minisat,[status(thm)],[c_97696,c_2431]) ).
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.43/4.51  
% 31.43/4.51  ------                               Statistics
% 31.43/4.51  
% 31.43/4.51  ------ General
% 31.43/4.51  
% 31.43/4.51  abstr_ref_over_cycles:                  0
% 31.43/4.51  abstr_ref_under_cycles:                 0
% 31.43/4.51  gc_basic_clause_elim:                   0
% 31.43/4.51  forced_gc_time:                         0
% 31.43/4.51  parsing_time:                           0.031
% 31.43/4.51  unif_index_cands_time:                  0.
% 31.43/4.51  unif_index_add_time:                    0.
% 31.43/4.51  orderings_time:                         0.
% 31.43/4.51  out_proof_time:                         0.018
% 31.43/4.51  total_time:                             3.801
% 31.43/4.51  num_of_symbols:                         57
% 31.43/4.51  num_of_terms:                           127787
% 31.43/4.51  
% 31.43/4.51  ------ Preprocessing
% 31.43/4.51  
% 31.43/4.51  num_of_splits:                          0
% 31.43/4.51  num_of_split_atoms:                     0
% 31.43/4.51  num_of_reused_defs:                     0
% 31.43/4.51  num_eq_ax_congr_red:                    43
% 31.43/4.51  num_of_sem_filtered_clauses:            1
% 31.43/4.51  num_of_subtypes:                        0
% 31.43/4.51  monotx_restored_types:                  0
% 31.43/4.51  sat_num_of_epr_types:                   0
% 31.43/4.51  sat_num_of_non_cyclic_types:            0
% 31.43/4.51  sat_guarded_non_collapsed_types:        0
% 31.43/4.51  num_pure_diseq_elim:                    0
% 31.43/4.51  simp_replaced_by:                       0
% 31.43/4.51  res_preprocessed:                       161
% 31.43/4.51  prep_upred:                             0
% 31.43/4.51  prep_unflattend:                        35
% 31.43/4.51  smt_new_axioms:                         0
% 31.43/4.51  pred_elim_cands:                        4
% 31.43/4.51  pred_elim:                              3
% 31.43/4.51  pred_elim_cl:                           4
% 31.43/4.51  pred_elim_cycles:                       5
% 31.43/4.51  merged_defs:                            8
% 31.43/4.51  merged_defs_ncl:                        0
% 31.43/4.51  bin_hyper_res:                          9
% 31.43/4.51  prep_cycles:                            4
% 31.43/4.51  pred_elim_time:                         0.02
% 31.43/4.51  splitting_time:                         0.
% 31.43/4.51  sem_filter_time:                        0.
% 31.43/4.51  monotx_time:                            0.001
% 31.43/4.51  subtype_inf_time:                       0.
% 31.43/4.51  
% 31.43/4.51  ------ Problem properties
% 31.43/4.51  
% 31.43/4.51  clauses:                                31
% 31.43/4.51  conjectures:                            7
% 31.43/4.51  epr:                                    6
% 31.43/4.51  horn:                                   28
% 31.43/4.51  ground:                                 13
% 31.43/4.51  unary:                                  10
% 31.43/4.51  binary:                                 9
% 31.43/4.51  lits:                                   68
% 31.43/4.51  lits_eq:                                27
% 31.43/4.51  fd_pure:                                0
% 31.43/4.51  fd_pseudo:                              0
% 31.43/4.51  fd_cond:                                0
% 31.43/4.51  fd_pseudo_cond:                         1
% 31.43/4.51  ac_symbols:                             0
% 31.43/4.51  
% 31.43/4.51  ------ Propositional Solver
% 31.43/4.51  
% 31.43/4.51  prop_solver_calls:                      49
% 31.43/4.51  prop_fast_solver_calls:                 2763
% 31.43/4.51  smt_solver_calls:                       0
% 31.43/4.51  smt_fast_solver_calls:                  0
% 31.43/4.51  prop_num_of_clauses:                    46047
% 31.43/4.51  prop_preprocess_simplified:             47088
% 31.43/4.51  prop_fo_subsumed:                       128
% 31.43/4.51  prop_solver_time:                       0.
% 31.43/4.51  smt_solver_time:                        0.
% 31.43/4.51  smt_fast_solver_time:                   0.
% 31.43/4.51  prop_fast_solver_time:                  0.
% 31.43/4.51  prop_unsat_core_time:                   0.005
% 31.43/4.51  
% 31.43/4.51  ------ QBF
% 31.43/4.51  
% 31.43/4.51  qbf_q_res:                              0
% 31.43/4.51  qbf_num_tautologies:                    0
% 31.43/4.51  qbf_prep_cycles:                        0
% 31.43/4.51  
% 31.43/4.51  ------ BMC1
% 31.43/4.51  
% 31.43/4.51  bmc1_current_bound:                     -1
% 31.43/4.51  bmc1_last_solved_bound:                 -1
% 31.43/4.51  bmc1_unsat_core_size:                   -1
% 31.43/4.51  bmc1_unsat_core_parents_size:           -1
% 31.43/4.51  bmc1_merge_next_fun:                    0
% 31.43/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.43/4.51  
% 31.43/4.51  ------ Instantiation
% 31.43/4.51  
% 31.43/4.51  inst_num_of_clauses:                    4115
% 31.43/4.51  inst_num_in_passive:                    342
% 31.43/4.51  inst_num_in_active:                     4416
% 31.43/4.51  inst_num_in_unprocessed:                2004
% 31.43/4.51  inst_num_of_loops:                      4809
% 31.43/4.51  inst_num_of_learning_restarts:          1
% 31.43/4.51  inst_num_moves_active_passive:          379
% 31.43/4.51  inst_lit_activity:                      0
% 31.43/4.51  inst_lit_activity_moves:                1
% 31.43/4.51  inst_num_tautologies:                   0
% 31.43/4.51  inst_num_prop_implied:                  0
% 31.43/4.51  inst_num_existing_simplified:           0
% 31.43/4.51  inst_num_eq_res_simplified:             0
% 31.43/4.51  inst_num_child_elim:                    0
% 31.43/4.51  inst_num_of_dismatching_blockings:      9836
% 31.43/4.51  inst_num_of_non_proper_insts:           15505
% 31.43/4.51  inst_num_of_duplicates:                 0
% 31.43/4.51  inst_inst_num_from_inst_to_res:         0
% 31.43/4.51  inst_dismatching_checking_time:         0.
% 31.43/4.51  
% 31.43/4.51  ------ Resolution
% 31.43/4.51  
% 31.43/4.51  res_num_of_clauses:                     47
% 31.43/4.51  res_num_in_passive:                     47
% 31.43/4.51  res_num_in_active:                      0
% 31.43/4.51  res_num_of_loops:                       165
% 31.43/4.51  res_forward_subset_subsumed:            755
% 31.43/4.51  res_backward_subset_subsumed:           2
% 31.43/4.51  res_forward_subsumed:                   0
% 31.43/4.51  res_backward_subsumed:                  0
% 31.43/4.51  res_forward_subsumption_resolution:     0
% 31.43/4.51  res_backward_subsumption_resolution:    0
% 31.43/4.51  res_clause_to_clause_subsumption:       25654
% 31.43/4.51  res_orphan_elimination:                 0
% 31.43/4.51  res_tautology_del:                      1458
% 31.43/4.51  res_num_eq_res_simplified:              0
% 31.43/4.51  res_num_sel_changes:                    0
% 31.43/4.51  res_moves_from_active_to_pass:          0
% 31.43/4.51  
% 31.43/4.51  ------ Superposition
% 31.43/4.51  
% 31.43/4.51  sup_time_total:                         0.
% 31.43/4.51  sup_time_generating:                    0.
% 31.43/4.51  sup_time_sim_full:                      0.
% 31.43/4.51  sup_time_sim_immed:                     0.
% 31.43/4.51  
% 31.43/4.51  sup_num_of_clauses:                     9840
% 31.43/4.51  sup_num_in_active:                      948
% 31.43/4.51  sup_num_in_passive:                     8892
% 31.43/4.51  sup_num_of_loops:                       960
% 31.43/4.51  sup_fw_superposition:                   8205
% 31.43/4.51  sup_bw_superposition:                   6332
% 31.43/4.51  sup_immediate_simplified:               4973
% 31.43/4.51  sup_given_eliminated:                   1
% 31.43/4.51  comparisons_done:                       0
% 31.43/4.51  comparisons_avoided:                    3
% 31.43/4.51  
% 31.43/4.51  ------ Simplifications
% 31.43/4.51  
% 31.43/4.51  
% 31.43/4.51  sim_fw_subset_subsumed:                 40
% 31.43/4.51  sim_bw_subset_subsumed:                 8
% 31.43/4.51  sim_fw_subsumed:                        10
% 31.43/4.51  sim_bw_subsumed:                        2
% 31.43/4.51  sim_fw_subsumption_res:                 0
% 31.43/4.51  sim_bw_subsumption_res:                 0
% 31.43/4.51  sim_tautology_del:                      2
% 31.43/4.51  sim_eq_tautology_del:                   547
% 31.43/4.51  sim_eq_res_simp:                        0
% 31.43/4.51  sim_fw_demodulated:                     1595
% 31.43/4.51  sim_bw_demodulated:                     590
% 31.43/4.51  sim_light_normalised:                   2902
% 31.43/4.51  sim_joinable_taut:                      0
% 31.43/4.51  sim_joinable_simp:                      0
% 31.43/4.51  sim_ac_normalised:                      0
% 31.43/4.51  sim_smt_subsumption:                    0
% 31.43/4.51  
%------------------------------------------------------------------------------
