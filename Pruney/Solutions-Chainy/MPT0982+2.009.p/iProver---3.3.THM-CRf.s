%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:39 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  185 (1349 expanded)
%              Number of clauses        :  108 ( 419 expanded)
%              Number of leaves         :   19 ( 328 expanded)
%              Depth                    :   22
%              Number of atoms          :  607 (9152 expanded)
%              Number of equality atoms :  277 (3117 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1229,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_408,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_16])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_408])).

cnf(c_1227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_2567,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1227])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1230,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1242,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3218,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1242])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1231,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1237,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1952,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1231,c_1237])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_501,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_33,c_30])).

cnf(c_1954,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1952,c_501])).

cnf(c_3220,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = sK1
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3218,c_1954])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1238,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1559,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1238])).

cnf(c_3788,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_45,c_1559])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1244,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3932,plain,
    ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1244])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1243,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3373,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1243])).

cnf(c_3575,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_45,c_1559])).

cnf(c_3933,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3932,c_3575])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4107,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4108,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4107])).

cnf(c_6202,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3933,c_42,c_45,c_1559,c_4108])).

cnf(c_6203,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6202])).

cnf(c_6209,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_6203])).

cnf(c_1560,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1238])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1249,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2024,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1559,c_1249])).

cnf(c_2175,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1560,c_2024])).

cnf(c_6211,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6209,c_2175])).

cnf(c_1561,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1559])).

cnf(c_6216,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6211])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7673,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_47005,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6211,c_35,c_31,c_1561,c_6216,c_7673])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1233,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4040,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1233])).

cnf(c_4272,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4040,c_42])).

cnf(c_4273,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4272])).

cnf(c_4280,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_4273])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4371,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_39])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4374,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4371,c_1235])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7537,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4374,c_39,c_41,c_42,c_44])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1236,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7544,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_7537,c_1236])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4373,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4371,c_32])).

cnf(c_7548,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7544,c_4373])).

cnf(c_1245,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2573,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1249])).

cnf(c_5179,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_2573])).

cnf(c_5433,plain,
    ( v1_relat_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5179,c_45,c_1559])).

cnf(c_5434,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5433])).

cnf(c_5440,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_1559,c_5434])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1240,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3359,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1240])).

cnf(c_3361,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3359,c_1954])).

cnf(c_5016,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3361,c_45,c_1559])).

cnf(c_5443,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5440,c_5016])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1248,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7619,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7548,c_1248])).

cnf(c_7687,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7619,c_1559,c_1560])).

cnf(c_2566,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1227])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1251,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2790,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_1251])).

cnf(c_7693,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_7687,c_2790])).

cnf(c_10969,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5443,c_5443,c_7693])).

cnf(c_47007,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_47005,c_7548,c_10969])).

cnf(c_1611,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1229,c_1236])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1751,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1611,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47007,c_1751])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:12:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.49/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/2.48  
% 15.49/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.48  
% 15.49/2.48  ------  iProver source info
% 15.49/2.48  
% 15.49/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.48  git: non_committed_changes: false
% 15.49/2.48  git: last_make_outside_of_git: false
% 15.49/2.48  
% 15.49/2.48  ------ 
% 15.49/2.48  
% 15.49/2.48  ------ Input Options
% 15.49/2.48  
% 15.49/2.48  --out_options                           all
% 15.49/2.48  --tptp_safe_out                         true
% 15.49/2.48  --problem_path                          ""
% 15.49/2.48  --include_path                          ""
% 15.49/2.48  --clausifier                            res/vclausify_rel
% 15.49/2.48  --clausifier_options                    ""
% 15.49/2.48  --stdin                                 false
% 15.49/2.48  --stats_out                             all
% 15.49/2.48  
% 15.49/2.48  ------ General Options
% 15.49/2.48  
% 15.49/2.48  --fof                                   false
% 15.49/2.48  --time_out_real                         305.
% 15.49/2.48  --time_out_virtual                      -1.
% 15.49/2.48  --symbol_type_check                     false
% 15.49/2.48  --clausify_out                          false
% 15.49/2.48  --sig_cnt_out                           false
% 15.49/2.48  --trig_cnt_out                          false
% 15.49/2.48  --trig_cnt_out_tolerance                1.
% 15.49/2.48  --trig_cnt_out_sk_spl                   false
% 15.49/2.48  --abstr_cl_out                          false
% 15.49/2.48  
% 15.49/2.48  ------ Global Options
% 15.49/2.48  
% 15.49/2.48  --schedule                              default
% 15.49/2.48  --add_important_lit                     false
% 15.49/2.48  --prop_solver_per_cl                    1000
% 15.49/2.48  --min_unsat_core                        false
% 15.49/2.48  --soft_assumptions                      false
% 15.49/2.48  --soft_lemma_size                       3
% 15.49/2.48  --prop_impl_unit_size                   0
% 15.49/2.48  --prop_impl_unit                        []
% 15.49/2.48  --share_sel_clauses                     true
% 15.49/2.48  --reset_solvers                         false
% 15.49/2.48  --bc_imp_inh                            [conj_cone]
% 15.49/2.48  --conj_cone_tolerance                   3.
% 15.49/2.48  --extra_neg_conj                        none
% 15.49/2.48  --large_theory_mode                     true
% 15.49/2.48  --prolific_symb_bound                   200
% 15.49/2.48  --lt_threshold                          2000
% 15.49/2.48  --clause_weak_htbl                      true
% 15.49/2.48  --gc_record_bc_elim                     false
% 15.49/2.48  
% 15.49/2.48  ------ Preprocessing Options
% 15.49/2.48  
% 15.49/2.48  --preprocessing_flag                    true
% 15.49/2.48  --time_out_prep_mult                    0.1
% 15.49/2.48  --splitting_mode                        input
% 15.49/2.48  --splitting_grd                         true
% 15.49/2.48  --splitting_cvd                         false
% 15.49/2.48  --splitting_cvd_svl                     false
% 15.49/2.48  --splitting_nvd                         32
% 15.49/2.48  --sub_typing                            true
% 15.49/2.48  --prep_gs_sim                           true
% 15.49/2.48  --prep_unflatten                        true
% 15.49/2.48  --prep_res_sim                          true
% 15.49/2.48  --prep_upred                            true
% 15.49/2.48  --prep_sem_filter                       exhaustive
% 15.49/2.48  --prep_sem_filter_out                   false
% 15.49/2.48  --pred_elim                             true
% 15.49/2.48  --res_sim_input                         true
% 15.49/2.48  --eq_ax_congr_red                       true
% 15.49/2.48  --pure_diseq_elim                       true
% 15.49/2.48  --brand_transform                       false
% 15.49/2.48  --non_eq_to_eq                          false
% 15.49/2.48  --prep_def_merge                        true
% 15.49/2.48  --prep_def_merge_prop_impl              false
% 15.49/2.48  --prep_def_merge_mbd                    true
% 15.49/2.48  --prep_def_merge_tr_red                 false
% 15.49/2.48  --prep_def_merge_tr_cl                  false
% 15.49/2.48  --smt_preprocessing                     true
% 15.49/2.48  --smt_ac_axioms                         fast
% 15.49/2.48  --preprocessed_out                      false
% 15.49/2.48  --preprocessed_stats                    false
% 15.49/2.48  
% 15.49/2.48  ------ Abstraction refinement Options
% 15.49/2.48  
% 15.49/2.48  --abstr_ref                             []
% 15.49/2.48  --abstr_ref_prep                        false
% 15.49/2.48  --abstr_ref_until_sat                   false
% 15.49/2.48  --abstr_ref_sig_restrict                funpre
% 15.49/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.48  --abstr_ref_under                       []
% 15.49/2.48  
% 15.49/2.48  ------ SAT Options
% 15.49/2.48  
% 15.49/2.48  --sat_mode                              false
% 15.49/2.48  --sat_fm_restart_options                ""
% 15.49/2.48  --sat_gr_def                            false
% 15.49/2.48  --sat_epr_types                         true
% 15.49/2.48  --sat_non_cyclic_types                  false
% 15.49/2.48  --sat_finite_models                     false
% 15.49/2.48  --sat_fm_lemmas                         false
% 15.49/2.48  --sat_fm_prep                           false
% 15.49/2.48  --sat_fm_uc_incr                        true
% 15.49/2.48  --sat_out_model                         small
% 15.49/2.48  --sat_out_clauses                       false
% 15.49/2.48  
% 15.49/2.48  ------ QBF Options
% 15.49/2.48  
% 15.49/2.48  --qbf_mode                              false
% 15.49/2.48  --qbf_elim_univ                         false
% 15.49/2.48  --qbf_dom_inst                          none
% 15.49/2.48  --qbf_dom_pre_inst                      false
% 15.49/2.48  --qbf_sk_in                             false
% 15.49/2.48  --qbf_pred_elim                         true
% 15.49/2.48  --qbf_split                             512
% 15.49/2.48  
% 15.49/2.48  ------ BMC1 Options
% 15.49/2.48  
% 15.49/2.48  --bmc1_incremental                      false
% 15.49/2.48  --bmc1_axioms                           reachable_all
% 15.49/2.48  --bmc1_min_bound                        0
% 15.49/2.48  --bmc1_max_bound                        -1
% 15.49/2.48  --bmc1_max_bound_default                -1
% 15.49/2.48  --bmc1_symbol_reachability              true
% 15.49/2.48  --bmc1_property_lemmas                  false
% 15.49/2.48  --bmc1_k_induction                      false
% 15.49/2.48  --bmc1_non_equiv_states                 false
% 15.49/2.48  --bmc1_deadlock                         false
% 15.49/2.48  --bmc1_ucm                              false
% 15.49/2.48  --bmc1_add_unsat_core                   none
% 15.49/2.48  --bmc1_unsat_core_children              false
% 15.49/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.48  --bmc1_out_stat                         full
% 15.49/2.48  --bmc1_ground_init                      false
% 15.49/2.48  --bmc1_pre_inst_next_state              false
% 15.49/2.48  --bmc1_pre_inst_state                   false
% 15.49/2.48  --bmc1_pre_inst_reach_state             false
% 15.49/2.48  --bmc1_out_unsat_core                   false
% 15.49/2.48  --bmc1_aig_witness_out                  false
% 15.49/2.48  --bmc1_verbose                          false
% 15.49/2.48  --bmc1_dump_clauses_tptp                false
% 15.49/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.48  --bmc1_dump_file                        -
% 15.49/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.48  --bmc1_ucm_extend_mode                  1
% 15.49/2.48  --bmc1_ucm_init_mode                    2
% 15.49/2.48  --bmc1_ucm_cone_mode                    none
% 15.49/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.48  --bmc1_ucm_relax_model                  4
% 15.49/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.48  --bmc1_ucm_layered_model                none
% 15.49/2.48  --bmc1_ucm_max_lemma_size               10
% 15.49/2.48  
% 15.49/2.48  ------ AIG Options
% 15.49/2.48  
% 15.49/2.48  --aig_mode                              false
% 15.49/2.48  
% 15.49/2.48  ------ Instantiation Options
% 15.49/2.48  
% 15.49/2.48  --instantiation_flag                    true
% 15.49/2.48  --inst_sos_flag                         true
% 15.49/2.48  --inst_sos_phase                        true
% 15.49/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.48  --inst_lit_sel_side                     num_symb
% 15.49/2.48  --inst_solver_per_active                1400
% 15.49/2.48  --inst_solver_calls_frac                1.
% 15.49/2.48  --inst_passive_queue_type               priority_queues
% 15.49/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.48  --inst_passive_queues_freq              [25;2]
% 15.49/2.48  --inst_dismatching                      true
% 15.49/2.48  --inst_eager_unprocessed_to_passive     true
% 15.49/2.48  --inst_prop_sim_given                   true
% 15.49/2.48  --inst_prop_sim_new                     false
% 15.49/2.48  --inst_subs_new                         false
% 15.49/2.48  --inst_eq_res_simp                      false
% 15.49/2.48  --inst_subs_given                       false
% 15.49/2.48  --inst_orphan_elimination               true
% 15.49/2.48  --inst_learning_loop_flag               true
% 15.49/2.48  --inst_learning_start                   3000
% 15.49/2.48  --inst_learning_factor                  2
% 15.49/2.48  --inst_start_prop_sim_after_learn       3
% 15.49/2.48  --inst_sel_renew                        solver
% 15.49/2.48  --inst_lit_activity_flag                true
% 15.49/2.48  --inst_restr_to_given                   false
% 15.49/2.48  --inst_activity_threshold               500
% 15.49/2.48  --inst_out_proof                        true
% 15.49/2.48  
% 15.49/2.48  ------ Resolution Options
% 15.49/2.48  
% 15.49/2.48  --resolution_flag                       true
% 15.49/2.48  --res_lit_sel                           adaptive
% 15.49/2.48  --res_lit_sel_side                      none
% 15.49/2.48  --res_ordering                          kbo
% 15.49/2.48  --res_to_prop_solver                    active
% 15.49/2.48  --res_prop_simpl_new                    false
% 15.49/2.48  --res_prop_simpl_given                  true
% 15.49/2.48  --res_passive_queue_type                priority_queues
% 15.49/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.48  --res_passive_queues_freq               [15;5]
% 15.49/2.48  --res_forward_subs                      full
% 15.49/2.48  --res_backward_subs                     full
% 15.49/2.48  --res_forward_subs_resolution           true
% 15.49/2.48  --res_backward_subs_resolution          true
% 15.49/2.48  --res_orphan_elimination                true
% 15.49/2.48  --res_time_limit                        2.
% 15.49/2.48  --res_out_proof                         true
% 15.49/2.48  
% 15.49/2.48  ------ Superposition Options
% 15.49/2.48  
% 15.49/2.48  --superposition_flag                    true
% 15.49/2.48  --sup_passive_queue_type                priority_queues
% 15.49/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.48  --demod_completeness_check              fast
% 15.49/2.48  --demod_use_ground                      true
% 15.49/2.48  --sup_to_prop_solver                    passive
% 15.49/2.48  --sup_prop_simpl_new                    true
% 15.49/2.48  --sup_prop_simpl_given                  true
% 15.49/2.48  --sup_fun_splitting                     true
% 15.49/2.48  --sup_smt_interval                      50000
% 15.49/2.48  
% 15.49/2.48  ------ Superposition Simplification Setup
% 15.49/2.48  
% 15.49/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.48  --sup_immed_triv                        [TrivRules]
% 15.49/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.48  --sup_immed_bw_main                     []
% 15.49/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.48  --sup_input_bw                          []
% 15.49/2.48  
% 15.49/2.48  ------ Combination Options
% 15.49/2.48  
% 15.49/2.48  --comb_res_mult                         3
% 15.49/2.48  --comb_sup_mult                         2
% 15.49/2.48  --comb_inst_mult                        10
% 15.49/2.48  
% 15.49/2.48  ------ Debug Options
% 15.49/2.48  
% 15.49/2.48  --dbg_backtrace                         false
% 15.49/2.48  --dbg_dump_prop_clauses                 false
% 15.49/2.48  --dbg_dump_prop_clauses_file            -
% 15.49/2.48  --dbg_out_stat                          false
% 15.49/2.48  ------ Parsing...
% 15.49/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.48  
% 15.49/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.49/2.48  
% 15.49/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.48  
% 15.49/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.48  ------ Proving...
% 15.49/2.48  ------ Problem Properties 
% 15.49/2.48  
% 15.49/2.48  
% 15.49/2.48  clauses                                 34
% 15.49/2.48  conjectures                             8
% 15.49/2.48  EPR                                     6
% 15.49/2.48  Horn                                    31
% 15.49/2.48  unary                                   10
% 15.49/2.48  binary                                  5
% 15.49/2.48  lits                                    94
% 15.49/2.48  lits eq                                 27
% 15.49/2.48  fd_pure                                 0
% 15.49/2.48  fd_pseudo                               0
% 15.49/2.48  fd_cond                                 0
% 15.49/2.48  fd_pseudo_cond                          1
% 15.49/2.48  AC symbols                              0
% 15.49/2.48  
% 15.49/2.48  ------ Schedule dynamic 5 is on 
% 15.49/2.48  
% 15.49/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.49/2.48  
% 15.49/2.48  
% 15.49/2.48  ------ 
% 15.49/2.48  Current options:
% 15.49/2.48  ------ 
% 15.49/2.48  
% 15.49/2.48  ------ Input Options
% 15.49/2.48  
% 15.49/2.48  --out_options                           all
% 15.49/2.48  --tptp_safe_out                         true
% 15.49/2.48  --problem_path                          ""
% 15.49/2.48  --include_path                          ""
% 15.49/2.48  --clausifier                            res/vclausify_rel
% 15.49/2.48  --clausifier_options                    ""
% 15.49/2.48  --stdin                                 false
% 15.49/2.48  --stats_out                             all
% 15.49/2.48  
% 15.49/2.48  ------ General Options
% 15.49/2.48  
% 15.49/2.48  --fof                                   false
% 15.49/2.48  --time_out_real                         305.
% 15.49/2.48  --time_out_virtual                      -1.
% 15.49/2.48  --symbol_type_check                     false
% 15.49/2.48  --clausify_out                          false
% 15.49/2.48  --sig_cnt_out                           false
% 15.49/2.48  --trig_cnt_out                          false
% 15.49/2.48  --trig_cnt_out_tolerance                1.
% 15.49/2.48  --trig_cnt_out_sk_spl                   false
% 15.49/2.48  --abstr_cl_out                          false
% 15.49/2.48  
% 15.49/2.48  ------ Global Options
% 15.49/2.48  
% 15.49/2.48  --schedule                              default
% 15.49/2.48  --add_important_lit                     false
% 15.49/2.48  --prop_solver_per_cl                    1000
% 15.49/2.48  --min_unsat_core                        false
% 15.49/2.48  --soft_assumptions                      false
% 15.49/2.48  --soft_lemma_size                       3
% 15.49/2.48  --prop_impl_unit_size                   0
% 15.49/2.48  --prop_impl_unit                        []
% 15.49/2.48  --share_sel_clauses                     true
% 15.49/2.48  --reset_solvers                         false
% 15.49/2.48  --bc_imp_inh                            [conj_cone]
% 15.49/2.48  --conj_cone_tolerance                   3.
% 15.49/2.48  --extra_neg_conj                        none
% 15.49/2.48  --large_theory_mode                     true
% 15.49/2.48  --prolific_symb_bound                   200
% 15.49/2.48  --lt_threshold                          2000
% 15.49/2.48  --clause_weak_htbl                      true
% 15.49/2.48  --gc_record_bc_elim                     false
% 15.49/2.48  
% 15.49/2.48  ------ Preprocessing Options
% 15.49/2.48  
% 15.49/2.48  --preprocessing_flag                    true
% 15.49/2.48  --time_out_prep_mult                    0.1
% 15.49/2.48  --splitting_mode                        input
% 15.49/2.48  --splitting_grd                         true
% 15.49/2.48  --splitting_cvd                         false
% 15.49/2.48  --splitting_cvd_svl                     false
% 15.49/2.48  --splitting_nvd                         32
% 15.49/2.48  --sub_typing                            true
% 15.49/2.48  --prep_gs_sim                           true
% 15.49/2.48  --prep_unflatten                        true
% 15.49/2.48  --prep_res_sim                          true
% 15.49/2.48  --prep_upred                            true
% 15.49/2.48  --prep_sem_filter                       exhaustive
% 15.49/2.48  --prep_sem_filter_out                   false
% 15.49/2.48  --pred_elim                             true
% 15.49/2.48  --res_sim_input                         true
% 15.49/2.48  --eq_ax_congr_red                       true
% 15.49/2.48  --pure_diseq_elim                       true
% 15.49/2.48  --brand_transform                       false
% 15.49/2.48  --non_eq_to_eq                          false
% 15.49/2.48  --prep_def_merge                        true
% 15.49/2.48  --prep_def_merge_prop_impl              false
% 15.49/2.48  --prep_def_merge_mbd                    true
% 15.49/2.48  --prep_def_merge_tr_red                 false
% 15.49/2.48  --prep_def_merge_tr_cl                  false
% 15.49/2.48  --smt_preprocessing                     true
% 15.49/2.48  --smt_ac_axioms                         fast
% 15.49/2.48  --preprocessed_out                      false
% 15.49/2.48  --preprocessed_stats                    false
% 15.49/2.48  
% 15.49/2.48  ------ Abstraction refinement Options
% 15.49/2.48  
% 15.49/2.48  --abstr_ref                             []
% 15.49/2.48  --abstr_ref_prep                        false
% 15.49/2.48  --abstr_ref_until_sat                   false
% 15.49/2.48  --abstr_ref_sig_restrict                funpre
% 15.49/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.48  --abstr_ref_under                       []
% 15.49/2.48  
% 15.49/2.48  ------ SAT Options
% 15.49/2.48  
% 15.49/2.48  --sat_mode                              false
% 15.49/2.48  --sat_fm_restart_options                ""
% 15.49/2.48  --sat_gr_def                            false
% 15.49/2.48  --sat_epr_types                         true
% 15.49/2.48  --sat_non_cyclic_types                  false
% 15.49/2.48  --sat_finite_models                     false
% 15.49/2.48  --sat_fm_lemmas                         false
% 15.49/2.48  --sat_fm_prep                           false
% 15.49/2.48  --sat_fm_uc_incr                        true
% 15.49/2.48  --sat_out_model                         small
% 15.49/2.48  --sat_out_clauses                       false
% 15.49/2.48  
% 15.49/2.48  ------ QBF Options
% 15.49/2.48  
% 15.49/2.48  --qbf_mode                              false
% 15.49/2.48  --qbf_elim_univ                         false
% 15.49/2.48  --qbf_dom_inst                          none
% 15.49/2.48  --qbf_dom_pre_inst                      false
% 15.49/2.48  --qbf_sk_in                             false
% 15.49/2.48  --qbf_pred_elim                         true
% 15.49/2.48  --qbf_split                             512
% 15.49/2.48  
% 15.49/2.48  ------ BMC1 Options
% 15.49/2.48  
% 15.49/2.48  --bmc1_incremental                      false
% 15.49/2.48  --bmc1_axioms                           reachable_all
% 15.49/2.48  --bmc1_min_bound                        0
% 15.49/2.48  --bmc1_max_bound                        -1
% 15.49/2.48  --bmc1_max_bound_default                -1
% 15.49/2.48  --bmc1_symbol_reachability              true
% 15.49/2.48  --bmc1_property_lemmas                  false
% 15.49/2.48  --bmc1_k_induction                      false
% 15.49/2.48  --bmc1_non_equiv_states                 false
% 15.49/2.48  --bmc1_deadlock                         false
% 15.49/2.48  --bmc1_ucm                              false
% 15.49/2.48  --bmc1_add_unsat_core                   none
% 15.49/2.48  --bmc1_unsat_core_children              false
% 15.49/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.48  --bmc1_out_stat                         full
% 15.49/2.48  --bmc1_ground_init                      false
% 15.49/2.48  --bmc1_pre_inst_next_state              false
% 15.49/2.48  --bmc1_pre_inst_state                   false
% 15.49/2.48  --bmc1_pre_inst_reach_state             false
% 15.49/2.48  --bmc1_out_unsat_core                   false
% 15.49/2.48  --bmc1_aig_witness_out                  false
% 15.49/2.48  --bmc1_verbose                          false
% 15.49/2.48  --bmc1_dump_clauses_tptp                false
% 15.49/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.48  --bmc1_dump_file                        -
% 15.49/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.48  --bmc1_ucm_extend_mode                  1
% 15.49/2.48  --bmc1_ucm_init_mode                    2
% 15.49/2.48  --bmc1_ucm_cone_mode                    none
% 15.49/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.48  --bmc1_ucm_relax_model                  4
% 15.49/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.48  --bmc1_ucm_layered_model                none
% 15.49/2.48  --bmc1_ucm_max_lemma_size               10
% 15.49/2.48  
% 15.49/2.48  ------ AIG Options
% 15.49/2.48  
% 15.49/2.48  --aig_mode                              false
% 15.49/2.48  
% 15.49/2.48  ------ Instantiation Options
% 15.49/2.48  
% 15.49/2.48  --instantiation_flag                    true
% 15.49/2.48  --inst_sos_flag                         true
% 15.49/2.48  --inst_sos_phase                        true
% 15.49/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.48  --inst_lit_sel_side                     none
% 15.49/2.48  --inst_solver_per_active                1400
% 15.49/2.48  --inst_solver_calls_frac                1.
% 15.49/2.48  --inst_passive_queue_type               priority_queues
% 15.49/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.48  --inst_passive_queues_freq              [25;2]
% 15.49/2.48  --inst_dismatching                      true
% 15.49/2.48  --inst_eager_unprocessed_to_passive     true
% 15.49/2.48  --inst_prop_sim_given                   true
% 15.49/2.48  --inst_prop_sim_new                     false
% 15.49/2.48  --inst_subs_new                         false
% 15.49/2.48  --inst_eq_res_simp                      false
% 15.49/2.48  --inst_subs_given                       false
% 15.49/2.48  --inst_orphan_elimination               true
% 15.49/2.48  --inst_learning_loop_flag               true
% 15.49/2.48  --inst_learning_start                   3000
% 15.49/2.48  --inst_learning_factor                  2
% 15.49/2.48  --inst_start_prop_sim_after_learn       3
% 15.49/2.48  --inst_sel_renew                        solver
% 15.49/2.48  --inst_lit_activity_flag                true
% 15.49/2.48  --inst_restr_to_given                   false
% 15.49/2.48  --inst_activity_threshold               500
% 15.49/2.48  --inst_out_proof                        true
% 15.49/2.48  
% 15.49/2.48  ------ Resolution Options
% 15.49/2.48  
% 15.49/2.48  --resolution_flag                       false
% 15.49/2.48  --res_lit_sel                           adaptive
% 15.49/2.48  --res_lit_sel_side                      none
% 15.49/2.48  --res_ordering                          kbo
% 15.49/2.48  --res_to_prop_solver                    active
% 15.49/2.48  --res_prop_simpl_new                    false
% 15.49/2.48  --res_prop_simpl_given                  true
% 15.49/2.49  --res_passive_queue_type                priority_queues
% 15.49/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.49  --res_passive_queues_freq               [15;5]
% 15.49/2.49  --res_forward_subs                      full
% 15.49/2.49  --res_backward_subs                     full
% 15.49/2.49  --res_forward_subs_resolution           true
% 15.49/2.49  --res_backward_subs_resolution          true
% 15.49/2.49  --res_orphan_elimination                true
% 15.49/2.49  --res_time_limit                        2.
% 15.49/2.49  --res_out_proof                         true
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Options
% 15.49/2.49  
% 15.49/2.49  --superposition_flag                    true
% 15.49/2.49  --sup_passive_queue_type                priority_queues
% 15.49/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.49  --demod_completeness_check              fast
% 15.49/2.49  --demod_use_ground                      true
% 15.49/2.49  --sup_to_prop_solver                    passive
% 15.49/2.49  --sup_prop_simpl_new                    true
% 15.49/2.49  --sup_prop_simpl_given                  true
% 15.49/2.49  --sup_fun_splitting                     true
% 15.49/2.49  --sup_smt_interval                      50000
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Simplification Setup
% 15.49/2.49  
% 15.49/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_immed_triv                        [TrivRules]
% 15.49/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_bw_main                     []
% 15.49/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_input_bw                          []
% 15.49/2.49  
% 15.49/2.49  ------ Combination Options
% 15.49/2.49  
% 15.49/2.49  --comb_res_mult                         3
% 15.49/2.49  --comb_sup_mult                         2
% 15.49/2.49  --comb_inst_mult                        10
% 15.49/2.49  
% 15.49/2.49  ------ Debug Options
% 15.49/2.49  
% 15.49/2.49  --dbg_backtrace                         false
% 15.49/2.49  --dbg_dump_prop_clauses                 false
% 15.49/2.49  --dbg_dump_prop_clauses_file            -
% 15.49/2.49  --dbg_out_stat                          false
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  ------ Proving...
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  % SZS status Theorem for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  fof(f17,conjecture,(
% 15.49/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f18,negated_conjecture,(
% 15.49/2.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 15.49/2.49    inference(negated_conjecture,[],[f17])).
% 15.49/2.49  
% 15.49/2.49  fof(f43,plain,(
% 15.49/2.49    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.49/2.49    inference(ennf_transformation,[],[f18])).
% 15.49/2.49  
% 15.49/2.49  fof(f44,plain,(
% 15.49/2.49    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.49/2.49    inference(flattening,[],[f43])).
% 15.49/2.49  
% 15.49/2.49  fof(f50,plain,(
% 15.49/2.49    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 15.49/2.49    introduced(choice_axiom,[])).
% 15.49/2.49  
% 15.49/2.49  fof(f49,plain,(
% 15.49/2.49    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.49/2.49    introduced(choice_axiom,[])).
% 15.49/2.49  
% 15.49/2.49  fof(f51,plain,(
% 15.49/2.49    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.49/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f50,f49])).
% 15.49/2.49  
% 15.49/2.49  fof(f83,plain,(
% 15.49/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f2,axiom,(
% 15.49/2.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f20,plain,(
% 15.49/2.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.49/2.49    inference(ennf_transformation,[],[f2])).
% 15.49/2.49  
% 15.49/2.49  fof(f47,plain,(
% 15.49/2.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.49/2.49    inference(nnf_transformation,[],[f20])).
% 15.49/2.49  
% 15.49/2.49  fof(f55,plain,(
% 15.49/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f47])).
% 15.49/2.49  
% 15.49/2.49  fof(f11,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f19,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.49/2.49    inference(pure_predicate_removal,[],[f11])).
% 15.49/2.49  
% 15.49/2.49  fof(f34,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f19])).
% 15.49/2.49  
% 15.49/2.49  fof(f69,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f34])).
% 15.49/2.49  
% 15.49/2.49  fof(f10,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f33,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f10])).
% 15.49/2.49  
% 15.49/2.49  fof(f68,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f33])).
% 15.49/2.49  
% 15.49/2.49  fof(f84,plain,(
% 15.49/2.49    v1_funct_1(sK4)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f8,axiom,(
% 15.49/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f29,plain,(
% 15.49/2.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f8])).
% 15.49/2.49  
% 15.49/2.49  fof(f30,plain,(
% 15.49/2.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f29])).
% 15.49/2.49  
% 15.49/2.49  fof(f65,plain,(
% 15.49/2.49    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f30])).
% 15.49/2.49  
% 15.49/2.49  fof(f86,plain,(
% 15.49/2.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f12,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f35,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f12])).
% 15.49/2.49  
% 15.49/2.49  fof(f70,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f35])).
% 15.49/2.49  
% 15.49/2.49  fof(f14,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f37,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f14])).
% 15.49/2.49  
% 15.49/2.49  fof(f38,plain,(
% 15.49/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(flattening,[],[f37])).
% 15.49/2.49  
% 15.49/2.49  fof(f48,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(nnf_transformation,[],[f38])).
% 15.49/2.49  
% 15.49/2.49  fof(f72,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f48])).
% 15.49/2.49  
% 15.49/2.49  fof(f85,plain,(
% 15.49/2.49    v1_funct_2(sK4,sK1,sK2)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f89,plain,(
% 15.49/2.49    k1_xboole_0 != sK2),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f88,plain,(
% 15.49/2.49    v2_funct_1(sK4)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f6,axiom,(
% 15.49/2.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f25,plain,(
% 15.49/2.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.49/2.49    inference(ennf_transformation,[],[f6])).
% 15.49/2.49  
% 15.49/2.49  fof(f26,plain,(
% 15.49/2.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.49/2.49    inference(flattening,[],[f25])).
% 15.49/2.49  
% 15.49/2.49  fof(f62,plain,(
% 15.49/2.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f26])).
% 15.49/2.49  
% 15.49/2.49  fof(f7,axiom,(
% 15.49/2.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f27,plain,(
% 15.49/2.49    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.49/2.49    inference(ennf_transformation,[],[f7])).
% 15.49/2.49  
% 15.49/2.49  fof(f28,plain,(
% 15.49/2.49    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.49/2.49    inference(flattening,[],[f27])).
% 15.49/2.49  
% 15.49/2.49  fof(f63,plain,(
% 15.49/2.49    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f28])).
% 15.49/2.49  
% 15.49/2.49  fof(f5,axiom,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f23,plain,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f5])).
% 15.49/2.49  
% 15.49/2.49  fof(f24,plain,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f23])).
% 15.49/2.49  
% 15.49/2.49  fof(f60,plain,(
% 15.49/2.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f24])).
% 15.49/2.49  
% 15.49/2.49  fof(f3,axiom,(
% 15.49/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f21,plain,(
% 15.49/2.49    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(ennf_transformation,[],[f3])).
% 15.49/2.49  
% 15.49/2.49  fof(f57,plain,(
% 15.49/2.49    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f21])).
% 15.49/2.49  
% 15.49/2.49  fof(f59,plain,(
% 15.49/2.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f24])).
% 15.49/2.49  
% 15.49/2.49  fof(f16,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f41,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.49/2.49    inference(ennf_transformation,[],[f16])).
% 15.49/2.49  
% 15.49/2.49  fof(f42,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.49/2.49    inference(flattening,[],[f41])).
% 15.49/2.49  
% 15.49/2.49  fof(f80,plain,(
% 15.49/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f42])).
% 15.49/2.49  
% 15.49/2.49  fof(f81,plain,(
% 15.49/2.49    v1_funct_1(sK3)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f15,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f39,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.49/2.49    inference(ennf_transformation,[],[f15])).
% 15.49/2.49  
% 15.49/2.49  fof(f40,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.49/2.49    inference(flattening,[],[f39])).
% 15.49/2.49  
% 15.49/2.49  fof(f79,plain,(
% 15.49/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f40])).
% 15.49/2.49  
% 15.49/2.49  fof(f13,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f36,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f13])).
% 15.49/2.49  
% 15.49/2.49  fof(f71,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f36])).
% 15.49/2.49  
% 15.49/2.49  fof(f87,plain,(
% 15.49/2.49    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f9,axiom,(
% 15.49/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f31,plain,(
% 15.49/2.49    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f9])).
% 15.49/2.49  
% 15.49/2.49  fof(f32,plain,(
% 15.49/2.49    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f31])).
% 15.49/2.49  
% 15.49/2.49  fof(f67,plain,(
% 15.49/2.49    ( ! [X0] : (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f32])).
% 15.49/2.49  
% 15.49/2.49  fof(f4,axiom,(
% 15.49/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f22,plain,(
% 15.49/2.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(ennf_transformation,[],[f4])).
% 15.49/2.49  
% 15.49/2.49  fof(f58,plain,(
% 15.49/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f22])).
% 15.49/2.49  
% 15.49/2.49  fof(f1,axiom,(
% 15.49/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f45,plain,(
% 15.49/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.49/2.49    inference(nnf_transformation,[],[f1])).
% 15.49/2.49  
% 15.49/2.49  fof(f46,plain,(
% 15.49/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.49/2.49    inference(flattening,[],[f45])).
% 15.49/2.49  
% 15.49/2.49  fof(f54,plain,(
% 15.49/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f46])).
% 15.49/2.49  
% 15.49/2.49  fof(f90,plain,(
% 15.49/2.49    k2_relset_1(sK0,sK1,sK3) != sK1),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  cnf(c_36,negated_conjecture,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1229,plain,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4,plain,
% 15.49/2.49      ( ~ v5_relat_1(X0,X1)
% 15.49/2.49      | r1_tarski(k2_relat_1(X0),X1)
% 15.49/2.49      | ~ v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_17,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | v5_relat_1(X0,X2) ),
% 15.49/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_403,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | r1_tarski(k2_relat_1(X3),X4)
% 15.49/2.49      | ~ v1_relat_1(X3)
% 15.49/2.49      | X0 != X3
% 15.49/2.49      | X2 != X4 ),
% 15.49/2.49      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_404,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | r1_tarski(k2_relat_1(X0),X2)
% 15.49/2.49      | ~ v1_relat_1(X0) ),
% 15.49/2.49      inference(unflattening,[status(thm)],[c_403]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_16,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_408,plain,
% 15.49/2.49      ( r1_tarski(k2_relat_1(X0),X2)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_404,c_16]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_409,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_408]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1227,plain,
% 15.49/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2567,plain,
% 15.49/2.49      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1229,c_1227]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_35,negated_conjecture,
% 15.49/2.49      ( v1_funct_1(sK4) ),
% 15.49/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1230,plain,
% 15.49/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_12,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1242,plain,
% 15.49/2.49      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3218,plain,
% 15.49/2.49      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1230,c_1242]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_33,negated_conjecture,
% 15.49/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1231,plain,
% 15.49/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_18,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1237,plain,
% 15.49/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1952,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1231,c_1237]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_25,plain,
% 15.49/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.49/2.49      | k1_xboole_0 = X2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_34,negated_conjecture,
% 15.49/2.49      ( v1_funct_2(sK4,sK1,sK2) ),
% 15.49/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_498,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.49/2.49      | sK4 != X0
% 15.49/2.49      | sK2 != X2
% 15.49/2.49      | sK1 != X1
% 15.49/2.49      | k1_xboole_0 = X2 ),
% 15.49/2.49      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_499,plain,
% 15.49/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 15.49/2.49      | k1_relset_1(sK1,sK2,sK4) = sK1
% 15.49/2.49      | k1_xboole_0 = sK2 ),
% 15.49/2.49      inference(unflattening,[status(thm)],[c_498]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_30,negated_conjecture,
% 15.49/2.49      ( k1_xboole_0 != sK2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_501,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_499,c_33,c_30]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1954,plain,
% 15.49/2.49      ( k1_relat_1(sK4) = sK1 ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_1952,c_501]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3220,plain,
% 15.49/2.49      ( k2_relat_1(k2_funct_1(sK4)) = sK1
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3218,c_1954]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_31,negated_conjecture,
% 15.49/2.49      ( v2_funct_1(sK4) ),
% 15.49/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_45,plain,
% 15.49/2.49      ( v2_funct_1(sK4) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1238,plain,
% 15.49/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1559,plain,
% 15.49/2.49      ( v1_relat_1(sK4) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1231,c_1238]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3788,plain,
% 15.49/2.49      ( k2_relat_1(k2_funct_1(sK4)) = sK1 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3220,c_45,c_1559]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_10,plain,
% 15.49/2.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 15.49/2.49      | ~ v1_funct_1(X1)
% 15.49/2.49      | ~ v1_relat_1(X1)
% 15.49/2.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 15.49/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1244,plain,
% 15.49/2.49      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 15.49/2.49      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3932,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
% 15.49/2.49      | r1_tarski(X0,sK1) != iProver_top
% 15.49/2.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_3788,c_1244]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_11,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 15.49/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1243,plain,
% 15.49/2.49      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3373,plain,
% 15.49/2.49      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1230,c_1243]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3575,plain,
% 15.49/2.49      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3373,c_45,c_1559]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3933,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 15.49/2.49      | r1_tarski(X0,sK1) != iProver_top
% 15.49/2.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3932,c_3575]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_42,plain,
% 15.49/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_8,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | v1_funct_1(k2_funct_1(X0))
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4107,plain,
% 15.49/2.49      ( v1_funct_1(k2_funct_1(sK4))
% 15.49/2.49      | ~ v1_funct_1(sK4)
% 15.49/2.49      | ~ v2_funct_1(sK4)
% 15.49/2.49      | ~ v1_relat_1(sK4) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4108,plain,
% 15.49/2.49      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 15.49/2.49      | v1_funct_1(sK4) != iProver_top
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_4107]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6202,plain,
% 15.49/2.49      ( r1_tarski(X0,sK1) != iProver_top
% 15.49/2.49      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3933,c_42,c_45,c_1559,c_4108]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6203,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 15.49/2.49      | r1_tarski(X0,sK1) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_6202]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6209,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3)
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2567,c_6203]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1560,plain,
% 15.49/2.49      ( v1_relat_1(sK3) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1229,c_1238]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5,plain,
% 15.49/2.49      ( ~ v1_relat_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X1)
% 15.49/2.49      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1249,plain,
% 15.49/2.49      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2024,plain,
% 15.49/2.49      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1559,c_1249]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2175,plain,
% 15.49/2.49      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1560,c_2024]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6211,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3)
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_6209,c_2175]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1561,plain,
% 15.49/2.49      ( v1_relat_1(sK4) ),
% 15.49/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_1559]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6216,plain,
% 15.49/2.49      ( ~ v1_relat_1(k2_funct_1(sK4))
% 15.49/2.49      | k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 15.49/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_6211]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_9,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | v1_relat_1(k2_funct_1(X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7673,plain,
% 15.49/2.49      ( ~ v1_funct_1(sK4)
% 15.49/2.49      | ~ v2_funct_1(sK4)
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK4))
% 15.49/2.49      | ~ v1_relat_1(sK4) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_47005,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_6211,c_35,c_31,c_1561,c_6216,c_7673]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_28,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v1_funct_1(X3)
% 15.49/2.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1233,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.49/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.49/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X5) != iProver_top
% 15.49/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4040,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v1_funct_1(sK4) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1231,c_1233]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4272,plain,
% 15.49/2.49      ( v1_funct_1(X2) != iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4040,c_42]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4273,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_4272]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4280,plain,
% 15.49/2.49      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1229,c_4273]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_38,negated_conjecture,
% 15.49/2.49      ( v1_funct_1(sK3) ),
% 15.49/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_39,plain,
% 15.49/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4371,plain,
% 15.49/2.49      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4280,c_39]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_26,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v1_funct_1(X3) ),
% 15.49/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1235,plain,
% 15.49/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.49/2.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4374,plain,
% 15.49/2.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 15.49/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 15.49/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.49/2.49      | v1_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_4371,c_1235]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_41,plain,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_44,plain,
% 15.49/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7537,plain,
% 15.49/2.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4374,c_39,c_41,c_42,c_44]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_19,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1236,plain,
% 15.49/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7544,plain,
% 15.49/2.49      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_7537,c_1236]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_32,negated_conjecture,
% 15.49/2.49      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4373,plain,
% 15.49/2.49      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_4371,c_32]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7548,plain,
% 15.49/2.49      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_7544,c_4373]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1245,plain,
% 15.49/2.49      ( v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2573,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1245,c_1249]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5179,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1230,c_2573]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5433,plain,
% 15.49/2.49      ( v1_relat_1(X0) != iProver_top
% 15.49/2.49      | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_5179,c_45,c_1559]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5434,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_5433]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5440,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1559,c_5434]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_14,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1240,plain,
% 15.49/2.49      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3359,plain,
% 15.49/2.49      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1230,c_1240]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3361,plain,
% 15.49/2.49      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1
% 15.49/2.49      | v2_funct_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3359,c_1954]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5016,plain,
% 15.49/2.49      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3361,c_45,c_1559]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5443,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = sK1 ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_5440,c_5016]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6,plain,
% 15.49/2.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 15.49/2.49      | ~ v1_relat_1(X1)
% 15.49/2.49      | ~ v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1248,plain,
% 15.49/2.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7619,plain,
% 15.49/2.49      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 15.49/2.49      | v1_relat_1(sK4) != iProver_top
% 15.49/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_7548,c_1248]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7687,plain,
% 15.49/2.49      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_7619,c_1559,c_1560]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2566,plain,
% 15.49/2.49      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1231,c_1227]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_0,plain,
% 15.49/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.49/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1251,plain,
% 15.49/2.49      ( X0 = X1
% 15.49/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.49/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2790,plain,
% 15.49/2.49      ( k2_relat_1(sK4) = sK2
% 15.49/2.49      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2566,c_1251]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7693,plain,
% 15.49/2.49      ( k2_relat_1(sK4) = sK2 ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_7687,c_2790]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_10969,plain,
% 15.49/2.49      ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_5443,c_5443,c_7693]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_47007,plain,
% 15.49/2.49      ( k2_relat_1(sK3) = sK1 ),
% 15.49/2.49      inference(light_normalisation,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_47005,c_7548,c_10969]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1611,plain,
% 15.49/2.49      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1229,c_1236]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_29,negated_conjecture,
% 15.49/2.49      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 15.49/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1751,plain,
% 15.49/2.49      ( k2_relat_1(sK3) != sK1 ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_1611,c_29]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(contradiction,plain,
% 15.49/2.49      ( $false ),
% 15.49/2.49      inference(minisat,[status(thm)],[c_47007,c_1751]) ).
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  ------                               Statistics
% 15.49/2.49  
% 15.49/2.49  ------ General
% 15.49/2.49  
% 15.49/2.49  abstr_ref_over_cycles:                  0
% 15.49/2.49  abstr_ref_under_cycles:                 0
% 15.49/2.49  gc_basic_clause_elim:                   0
% 15.49/2.49  forced_gc_time:                         0
% 15.49/2.49  parsing_time:                           0.009
% 15.49/2.49  unif_index_cands_time:                  0.
% 15.49/2.49  unif_index_add_time:                    0.
% 15.49/2.49  orderings_time:                         0.
% 15.49/2.49  out_proof_time:                         0.018
% 15.49/2.49  total_time:                             1.679
% 15.49/2.49  num_of_symbols:                         55
% 15.49/2.49  num_of_terms:                           48428
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing
% 15.49/2.49  
% 15.49/2.49  num_of_splits:                          0
% 15.49/2.49  num_of_split_atoms:                     0
% 15.49/2.49  num_of_reused_defs:                     0
% 15.49/2.49  num_eq_ax_congr_red:                    16
% 15.49/2.49  num_of_sem_filtered_clauses:            1
% 15.49/2.49  num_of_subtypes:                        0
% 15.49/2.49  monotx_restored_types:                  0
% 15.49/2.49  sat_num_of_epr_types:                   0
% 15.49/2.49  sat_num_of_non_cyclic_types:            0
% 15.49/2.49  sat_guarded_non_collapsed_types:        0
% 15.49/2.49  num_pure_diseq_elim:                    0
% 15.49/2.49  simp_replaced_by:                       0
% 15.49/2.49  res_preprocessed:                       175
% 15.49/2.49  prep_upred:                             0
% 15.49/2.49  prep_unflattend:                        36
% 15.49/2.49  smt_new_axioms:                         0
% 15.49/2.49  pred_elim_cands:                        5
% 15.49/2.49  pred_elim:                              2
% 15.49/2.49  pred_elim_cl:                           4
% 15.49/2.49  pred_elim_cycles:                       4
% 15.49/2.49  merged_defs:                            0
% 15.49/2.49  merged_defs_ncl:                        0
% 15.49/2.49  bin_hyper_res:                          0
% 15.49/2.49  prep_cycles:                            4
% 15.49/2.49  pred_elim_time:                         0.004
% 15.49/2.49  splitting_time:                         0.
% 15.49/2.49  sem_filter_time:                        0.
% 15.49/2.49  monotx_time:                            0.
% 15.49/2.49  subtype_inf_time:                       0.
% 15.49/2.49  
% 15.49/2.49  ------ Problem properties
% 15.49/2.49  
% 15.49/2.49  clauses:                                34
% 15.49/2.49  conjectures:                            8
% 15.49/2.49  epr:                                    6
% 15.49/2.49  horn:                                   31
% 15.49/2.49  ground:                                 14
% 15.49/2.49  unary:                                  10
% 15.49/2.49  binary:                                 5
% 15.49/2.49  lits:                                   94
% 15.49/2.49  lits_eq:                                27
% 15.49/2.49  fd_pure:                                0
% 15.49/2.49  fd_pseudo:                              0
% 15.49/2.49  fd_cond:                                0
% 15.49/2.49  fd_pseudo_cond:                         1
% 15.49/2.49  ac_symbols:                             0
% 15.49/2.49  
% 15.49/2.49  ------ Propositional Solver
% 15.49/2.49  
% 15.49/2.49  prop_solver_calls:                      48
% 15.49/2.49  prop_fast_solver_calls:                 3958
% 15.49/2.49  smt_solver_calls:                       0
% 15.49/2.49  smt_fast_solver_calls:                  0
% 15.49/2.49  prop_num_of_clauses:                    22378
% 15.49/2.49  prop_preprocess_simplified:             35300
% 15.49/2.49  prop_fo_subsumed:                       825
% 15.49/2.49  prop_solver_time:                       0.
% 15.49/2.49  smt_solver_time:                        0.
% 15.49/2.49  smt_fast_solver_time:                   0.
% 15.49/2.49  prop_fast_solver_time:                  0.
% 15.49/2.49  prop_unsat_core_time:                   0.003
% 15.49/2.49  
% 15.49/2.49  ------ QBF
% 15.49/2.49  
% 15.49/2.49  qbf_q_res:                              0
% 15.49/2.49  qbf_num_tautologies:                    0
% 15.49/2.49  qbf_prep_cycles:                        0
% 15.49/2.49  
% 15.49/2.49  ------ BMC1
% 15.49/2.49  
% 15.49/2.49  bmc1_current_bound:                     -1
% 15.49/2.49  bmc1_last_solved_bound:                 -1
% 15.49/2.49  bmc1_unsat_core_size:                   -1
% 15.49/2.49  bmc1_unsat_core_parents_size:           -1
% 15.49/2.49  bmc1_merge_next_fun:                    0
% 15.49/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.49/2.49  
% 15.49/2.49  ------ Instantiation
% 15.49/2.49  
% 15.49/2.49  inst_num_of_clauses:                    1238
% 15.49/2.49  inst_num_in_passive:                    462
% 15.49/2.49  inst_num_in_active:                     3266
% 15.49/2.49  inst_num_in_unprocessed:                192
% 15.49/2.49  inst_num_of_loops:                      3589
% 15.49/2.49  inst_num_of_learning_restarts:          1
% 15.49/2.49  inst_num_moves_active_passive:          309
% 15.49/2.49  inst_lit_activity:                      0
% 15.49/2.49  inst_lit_activity_moves:                1
% 15.49/2.49  inst_num_tautologies:                   0
% 15.49/2.49  inst_num_prop_implied:                  0
% 15.49/2.49  inst_num_existing_simplified:           0
% 15.49/2.49  inst_num_eq_res_simplified:             0
% 15.49/2.49  inst_num_child_elim:                    0
% 15.49/2.49  inst_num_of_dismatching_blockings:      3462
% 15.49/2.49  inst_num_of_non_proper_insts:           9223
% 15.49/2.49  inst_num_of_duplicates:                 0
% 15.49/2.49  inst_inst_num_from_inst_to_res:         0
% 15.49/2.49  inst_dismatching_checking_time:         0.
% 15.49/2.49  
% 15.49/2.49  ------ Resolution
% 15.49/2.49  
% 15.49/2.49  res_num_of_clauses:                     51
% 15.49/2.49  res_num_in_passive:                     51
% 15.49/2.49  res_num_in_active:                      0
% 15.49/2.49  res_num_of_loops:                       179
% 15.49/2.49  res_forward_subset_subsumed:            601
% 15.49/2.49  res_backward_subset_subsumed:           0
% 15.49/2.49  res_forward_subsumed:                   0
% 15.49/2.49  res_backward_subsumed:                  0
% 15.49/2.49  res_forward_subsumption_resolution:     0
% 15.49/2.49  res_backward_subsumption_resolution:    0
% 15.49/2.49  res_clause_to_clause_subsumption:       5962
% 15.49/2.49  res_orphan_elimination:                 0
% 15.49/2.49  res_tautology_del:                      1026
% 15.49/2.49  res_num_eq_res_simplified:              0
% 15.49/2.49  res_num_sel_changes:                    0
% 15.49/2.49  res_moves_from_active_to_pass:          0
% 15.49/2.49  
% 15.49/2.49  ------ Superposition
% 15.49/2.49  
% 15.49/2.49  sup_time_total:                         0.
% 15.49/2.49  sup_time_generating:                    0.
% 15.49/2.49  sup_time_sim_full:                      0.
% 15.49/2.49  sup_time_sim_immed:                     0.
% 15.49/2.49  
% 15.49/2.49  sup_num_of_clauses:                     2527
% 15.49/2.49  sup_num_in_active:                      682
% 15.49/2.49  sup_num_in_passive:                     1845
% 15.49/2.49  sup_num_of_loops:                       717
% 15.49/2.49  sup_fw_superposition:                   1154
% 15.49/2.49  sup_bw_superposition:                   1678
% 15.49/2.49  sup_immediate_simplified:               1125
% 15.49/2.49  sup_given_eliminated:                   1
% 15.49/2.49  comparisons_done:                       0
% 15.49/2.49  comparisons_avoided:                    3
% 15.49/2.49  
% 15.49/2.49  ------ Simplifications
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  sim_fw_subset_subsumed:                 37
% 15.49/2.49  sim_bw_subset_subsumed:                 128
% 15.49/2.49  sim_fw_subsumed:                        52
% 15.49/2.49  sim_bw_subsumed:                        0
% 15.49/2.49  sim_fw_subsumption_res:                 0
% 15.49/2.49  sim_bw_subsumption_res:                 0
% 15.49/2.49  sim_tautology_del:                      0
% 15.49/2.49  sim_eq_tautology_del:                   45
% 15.49/2.49  sim_eq_res_simp:                        0
% 15.49/2.49  sim_fw_demodulated:                     94
% 15.49/2.49  sim_bw_demodulated:                     27
% 15.49/2.49  sim_light_normalised:                   1141
% 15.49/2.49  sim_joinable_taut:                      0
% 15.49/2.49  sim_joinable_simp:                      0
% 15.49/2.49  sim_ac_normalised:                      0
% 15.49/2.49  sim_smt_subsumption:                    0
% 15.49/2.49  
%------------------------------------------------------------------------------
