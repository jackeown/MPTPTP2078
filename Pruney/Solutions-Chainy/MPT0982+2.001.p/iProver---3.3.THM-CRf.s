%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:37 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 919 expanded)
%              Number of clauses        :  102 ( 275 expanded)
%              Number of leaves         :   16 ( 222 expanded)
%              Depth                    :   20
%              Number of atoms          :  553 (6261 expanded)
%              Number of equality atoms :  248 (2112 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f43,f42])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1197,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1202,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2346,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1197,c_1202])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_543,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_28,c_25])).

cnf(c_2351,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2346,c_543])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2640,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2351,c_1198])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1412,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1413,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_3190,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2640,c_37,c_39,c_1413])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1207,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1200,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3415,plain,
    ( k4_relset_1(X0,X1,sK1,X2,X3,sK4) = k5_relat_1(X3,sK4)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_1200])).

cnf(c_8748,plain,
    ( k4_relset_1(sK1,sK2,sK1,X0,sK4,sK4) = k5_relat_1(sK4,sK4)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_3415])).

cnf(c_8868,plain,
    ( k4_relset_1(sK1,sK2,sK1,k2_relat_1(sK4),sK4,sK4) = k5_relat_1(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1207,c_8748])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8886,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8868,c_1203])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1415,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1416,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_5])).

cnf(c_371,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_8])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1435,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1485,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1631,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2578,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | sK1 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_2579,plain,
    ( sK1 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_762,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1467,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_3851,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_5638,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1192])).

cnf(c_1208,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5670,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5638,c_1208])).

cnf(c_1195,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3413,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1200])).

cnf(c_3976,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1195,c_3413])).

cnf(c_4177,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_1203])).

cnf(c_5976,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4177,c_36,c_39])).

cnf(c_1201,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5987,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5976,c_1201])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1199,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3771,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1199])).

cnf(c_4540,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3771,c_37])).

cnf(c_4541,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4540])).

cnf(c_4552,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_4541])).

cnf(c_1537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_3042,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2095])).

cnf(c_5126,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4552,c_33,c_31,c_30,c_28,c_3042])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5129,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5126,c_27])).

cnf(c_6009,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5987,c_5129])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_334,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_335,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( ~ v1_funct_1(X0)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_30])).

cnf(c_340,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_1193,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_336,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_2114,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1193,c_37,c_39,c_336,c_1413])).

cnf(c_2115,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2114])).

cnf(c_2636,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2351,c_2115])).

cnf(c_6048,plain,
    ( k2_relat_1(sK4) != sK2
    | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6009,c_2636])).

cnf(c_8749,plain,
    ( k4_relset_1(sK0,sK1,sK1,X0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_3415])).

cnf(c_8891,plain,
    ( k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1207,c_8749])).

cnf(c_5636,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1192])).

cnf(c_26441,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8891,c_5636])).

cnf(c_26835,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26441,c_6009])).

cnf(c_27197,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8886,c_34,c_31,c_36,c_24,c_1416,c_1435,c_1485,c_2579,c_3851,c_5670,c_6048,c_26835])).

cnf(c_27202,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_27197])).

cnf(c_1657,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1660,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27202,c_1660])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.41/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/2.01  
% 11.41/2.01  ------  iProver source info
% 11.41/2.01  
% 11.41/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.41/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/2.01  git: non_committed_changes: false
% 11.41/2.01  git: last_make_outside_of_git: false
% 11.41/2.01  
% 11.41/2.01  ------ 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options
% 11.41/2.01  
% 11.41/2.01  --out_options                           all
% 11.41/2.01  --tptp_safe_out                         true
% 11.41/2.01  --problem_path                          ""
% 11.41/2.01  --include_path                          ""
% 11.41/2.01  --clausifier                            res/vclausify_rel
% 11.41/2.01  --clausifier_options                    --mode clausify
% 11.41/2.01  --stdin                                 false
% 11.41/2.01  --stats_out                             all
% 11.41/2.01  
% 11.41/2.01  ------ General Options
% 11.41/2.01  
% 11.41/2.01  --fof                                   false
% 11.41/2.01  --time_out_real                         305.
% 11.41/2.01  --time_out_virtual                      -1.
% 11.41/2.01  --symbol_type_check                     false
% 11.41/2.01  --clausify_out                          false
% 11.41/2.01  --sig_cnt_out                           false
% 11.41/2.01  --trig_cnt_out                          false
% 11.41/2.01  --trig_cnt_out_tolerance                1.
% 11.41/2.01  --trig_cnt_out_sk_spl                   false
% 11.41/2.01  --abstr_cl_out                          false
% 11.41/2.01  
% 11.41/2.01  ------ Global Options
% 11.41/2.01  
% 11.41/2.01  --schedule                              default
% 11.41/2.01  --add_important_lit                     false
% 11.41/2.01  --prop_solver_per_cl                    1000
% 11.41/2.01  --min_unsat_core                        false
% 11.41/2.01  --soft_assumptions                      false
% 11.41/2.01  --soft_lemma_size                       3
% 11.41/2.01  --prop_impl_unit_size                   0
% 11.41/2.01  --prop_impl_unit                        []
% 11.41/2.01  --share_sel_clauses                     true
% 11.41/2.01  --reset_solvers                         false
% 11.41/2.01  --bc_imp_inh                            [conj_cone]
% 11.41/2.01  --conj_cone_tolerance                   3.
% 11.41/2.01  --extra_neg_conj                        none
% 11.41/2.01  --large_theory_mode                     true
% 11.41/2.01  --prolific_symb_bound                   200
% 11.41/2.01  --lt_threshold                          2000
% 11.41/2.01  --clause_weak_htbl                      true
% 11.41/2.01  --gc_record_bc_elim                     false
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing Options
% 11.41/2.01  
% 11.41/2.01  --preprocessing_flag                    true
% 11.41/2.01  --time_out_prep_mult                    0.1
% 11.41/2.01  --splitting_mode                        input
% 11.41/2.01  --splitting_grd                         true
% 11.41/2.01  --splitting_cvd                         false
% 11.41/2.01  --splitting_cvd_svl                     false
% 11.41/2.01  --splitting_nvd                         32
% 11.41/2.01  --sub_typing                            true
% 11.41/2.01  --prep_gs_sim                           true
% 11.41/2.01  --prep_unflatten                        true
% 11.41/2.01  --prep_res_sim                          true
% 11.41/2.01  --prep_upred                            true
% 11.41/2.01  --prep_sem_filter                       exhaustive
% 11.41/2.01  --prep_sem_filter_out                   false
% 11.41/2.01  --pred_elim                             true
% 11.41/2.01  --res_sim_input                         true
% 11.41/2.01  --eq_ax_congr_red                       true
% 11.41/2.01  --pure_diseq_elim                       true
% 11.41/2.01  --brand_transform                       false
% 11.41/2.01  --non_eq_to_eq                          false
% 11.41/2.01  --prep_def_merge                        true
% 11.41/2.01  --prep_def_merge_prop_impl              false
% 11.41/2.01  --prep_def_merge_mbd                    true
% 11.41/2.01  --prep_def_merge_tr_red                 false
% 11.41/2.01  --prep_def_merge_tr_cl                  false
% 11.41/2.01  --smt_preprocessing                     true
% 11.41/2.01  --smt_ac_axioms                         fast
% 11.41/2.01  --preprocessed_out                      false
% 11.41/2.01  --preprocessed_stats                    false
% 11.41/2.01  
% 11.41/2.01  ------ Abstraction refinement Options
% 11.41/2.01  
% 11.41/2.01  --abstr_ref                             []
% 11.41/2.01  --abstr_ref_prep                        false
% 11.41/2.01  --abstr_ref_until_sat                   false
% 11.41/2.01  --abstr_ref_sig_restrict                funpre
% 11.41/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/2.01  --abstr_ref_under                       []
% 11.41/2.01  
% 11.41/2.01  ------ SAT Options
% 11.41/2.01  
% 11.41/2.01  --sat_mode                              false
% 11.41/2.01  --sat_fm_restart_options                ""
% 11.41/2.01  --sat_gr_def                            false
% 11.41/2.01  --sat_epr_types                         true
% 11.41/2.01  --sat_non_cyclic_types                  false
% 11.41/2.01  --sat_finite_models                     false
% 11.41/2.01  --sat_fm_lemmas                         false
% 11.41/2.01  --sat_fm_prep                           false
% 11.41/2.01  --sat_fm_uc_incr                        true
% 11.41/2.01  --sat_out_model                         small
% 11.41/2.01  --sat_out_clauses                       false
% 11.41/2.01  
% 11.41/2.01  ------ QBF Options
% 11.41/2.01  
% 11.41/2.01  --qbf_mode                              false
% 11.41/2.01  --qbf_elim_univ                         false
% 11.41/2.01  --qbf_dom_inst                          none
% 11.41/2.01  --qbf_dom_pre_inst                      false
% 11.41/2.01  --qbf_sk_in                             false
% 11.41/2.01  --qbf_pred_elim                         true
% 11.41/2.01  --qbf_split                             512
% 11.41/2.01  
% 11.41/2.01  ------ BMC1 Options
% 11.41/2.01  
% 11.41/2.01  --bmc1_incremental                      false
% 11.41/2.01  --bmc1_axioms                           reachable_all
% 11.41/2.01  --bmc1_min_bound                        0
% 11.41/2.01  --bmc1_max_bound                        -1
% 11.41/2.01  --bmc1_max_bound_default                -1
% 11.41/2.01  --bmc1_symbol_reachability              true
% 11.41/2.01  --bmc1_property_lemmas                  false
% 11.41/2.01  --bmc1_k_induction                      false
% 11.41/2.01  --bmc1_non_equiv_states                 false
% 11.41/2.01  --bmc1_deadlock                         false
% 11.41/2.01  --bmc1_ucm                              false
% 11.41/2.01  --bmc1_add_unsat_core                   none
% 11.41/2.01  --bmc1_unsat_core_children              false
% 11.41/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/2.01  --bmc1_out_stat                         full
% 11.41/2.01  --bmc1_ground_init                      false
% 11.41/2.01  --bmc1_pre_inst_next_state              false
% 11.41/2.01  --bmc1_pre_inst_state                   false
% 11.41/2.01  --bmc1_pre_inst_reach_state             false
% 11.41/2.01  --bmc1_out_unsat_core                   false
% 11.41/2.01  --bmc1_aig_witness_out                  false
% 11.41/2.01  --bmc1_verbose                          false
% 11.41/2.01  --bmc1_dump_clauses_tptp                false
% 11.41/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.41/2.01  --bmc1_dump_file                        -
% 11.41/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.41/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.41/2.01  --bmc1_ucm_extend_mode                  1
% 11.41/2.01  --bmc1_ucm_init_mode                    2
% 11.41/2.01  --bmc1_ucm_cone_mode                    none
% 11.41/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.41/2.01  --bmc1_ucm_relax_model                  4
% 11.41/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.41/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/2.01  --bmc1_ucm_layered_model                none
% 11.41/2.01  --bmc1_ucm_max_lemma_size               10
% 11.41/2.01  
% 11.41/2.01  ------ AIG Options
% 11.41/2.01  
% 11.41/2.01  --aig_mode                              false
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation Options
% 11.41/2.01  
% 11.41/2.01  --instantiation_flag                    true
% 11.41/2.01  --inst_sos_flag                         false
% 11.41/2.01  --inst_sos_phase                        true
% 11.41/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel_side                     num_symb
% 11.41/2.01  --inst_solver_per_active                1400
% 11.41/2.01  --inst_solver_calls_frac                1.
% 11.41/2.01  --inst_passive_queue_type               priority_queues
% 11.41/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/2.01  --inst_passive_queues_freq              [25;2]
% 11.41/2.01  --inst_dismatching                      true
% 11.41/2.01  --inst_eager_unprocessed_to_passive     true
% 11.41/2.01  --inst_prop_sim_given                   true
% 11.41/2.01  --inst_prop_sim_new                     false
% 11.41/2.01  --inst_subs_new                         false
% 11.41/2.01  --inst_eq_res_simp                      false
% 11.41/2.01  --inst_subs_given                       false
% 11.41/2.01  --inst_orphan_elimination               true
% 11.41/2.01  --inst_learning_loop_flag               true
% 11.41/2.01  --inst_learning_start                   3000
% 11.41/2.01  --inst_learning_factor                  2
% 11.41/2.01  --inst_start_prop_sim_after_learn       3
% 11.41/2.01  --inst_sel_renew                        solver
% 11.41/2.01  --inst_lit_activity_flag                true
% 11.41/2.01  --inst_restr_to_given                   false
% 11.41/2.01  --inst_activity_threshold               500
% 11.41/2.01  --inst_out_proof                        true
% 11.41/2.01  
% 11.41/2.01  ------ Resolution Options
% 11.41/2.01  
% 11.41/2.01  --resolution_flag                       true
% 11.41/2.01  --res_lit_sel                           adaptive
% 11.41/2.01  --res_lit_sel_side                      none
% 11.41/2.01  --res_ordering                          kbo
% 11.41/2.01  --res_to_prop_solver                    active
% 11.41/2.01  --res_prop_simpl_new                    false
% 11.41/2.01  --res_prop_simpl_given                  true
% 11.41/2.01  --res_passive_queue_type                priority_queues
% 11.41/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/2.01  --res_passive_queues_freq               [15;5]
% 11.41/2.01  --res_forward_subs                      full
% 11.41/2.01  --res_backward_subs                     full
% 11.41/2.01  --res_forward_subs_resolution           true
% 11.41/2.01  --res_backward_subs_resolution          true
% 11.41/2.01  --res_orphan_elimination                true
% 11.41/2.01  --res_time_limit                        2.
% 11.41/2.01  --res_out_proof                         true
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Options
% 11.41/2.01  
% 11.41/2.01  --superposition_flag                    true
% 11.41/2.01  --sup_passive_queue_type                priority_queues
% 11.41/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.41/2.01  --demod_completeness_check              fast
% 11.41/2.01  --demod_use_ground                      true
% 11.41/2.01  --sup_to_prop_solver                    passive
% 11.41/2.01  --sup_prop_simpl_new                    true
% 11.41/2.01  --sup_prop_simpl_given                  true
% 11.41/2.01  --sup_fun_splitting                     false
% 11.41/2.01  --sup_smt_interval                      50000
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Simplification Setup
% 11.41/2.01  
% 11.41/2.01  --sup_indices_passive                   []
% 11.41/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_full_bw                           [BwDemod]
% 11.41/2.01  --sup_immed_triv                        [TrivRules]
% 11.41/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_immed_bw_main                     []
% 11.41/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/2.01  
% 11.41/2.01  ------ Combination Options
% 11.41/2.01  
% 11.41/2.01  --comb_res_mult                         3
% 11.41/2.01  --comb_sup_mult                         2
% 11.41/2.01  --comb_inst_mult                        10
% 11.41/2.01  
% 11.41/2.01  ------ Debug Options
% 11.41/2.01  
% 11.41/2.01  --dbg_backtrace                         false
% 11.41/2.01  --dbg_dump_prop_clauses                 false
% 11.41/2.01  --dbg_dump_prop_clauses_file            -
% 11.41/2.01  --dbg_out_stat                          false
% 11.41/2.01  ------ Parsing...
% 11.41/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.41/2.01  ------ Proving...
% 11.41/2.01  ------ Problem Properties 
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  clauses                                 29
% 11.41/2.01  conjectures                             7
% 11.41/2.01  EPR                                     5
% 11.41/2.01  Horn                                    24
% 11.41/2.01  unary                                   10
% 11.41/2.01  binary                                  5
% 11.41/2.01  lits                                    74
% 11.41/2.01  lits eq                                 28
% 11.41/2.01  fd_pure                                 0
% 11.41/2.01  fd_pseudo                               0
% 11.41/2.01  fd_cond                                 2
% 11.41/2.01  fd_pseudo_cond                          1
% 11.41/2.01  AC symbols                              0
% 11.41/2.01  
% 11.41/2.01  ------ Schedule dynamic 5 is on 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  ------ 
% 11.41/2.01  Current options:
% 11.41/2.01  ------ 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options
% 11.41/2.01  
% 11.41/2.01  --out_options                           all
% 11.41/2.01  --tptp_safe_out                         true
% 11.41/2.01  --problem_path                          ""
% 11.41/2.01  --include_path                          ""
% 11.41/2.01  --clausifier                            res/vclausify_rel
% 11.41/2.01  --clausifier_options                    --mode clausify
% 11.41/2.01  --stdin                                 false
% 11.41/2.01  --stats_out                             all
% 11.41/2.01  
% 11.41/2.01  ------ General Options
% 11.41/2.01  
% 11.41/2.01  --fof                                   false
% 11.41/2.01  --time_out_real                         305.
% 11.41/2.01  --time_out_virtual                      -1.
% 11.41/2.01  --symbol_type_check                     false
% 11.41/2.01  --clausify_out                          false
% 11.41/2.01  --sig_cnt_out                           false
% 11.41/2.01  --trig_cnt_out                          false
% 11.41/2.01  --trig_cnt_out_tolerance                1.
% 11.41/2.01  --trig_cnt_out_sk_spl                   false
% 11.41/2.01  --abstr_cl_out                          false
% 11.41/2.01  
% 11.41/2.01  ------ Global Options
% 11.41/2.01  
% 11.41/2.01  --schedule                              default
% 11.41/2.01  --add_important_lit                     false
% 11.41/2.01  --prop_solver_per_cl                    1000
% 11.41/2.01  --min_unsat_core                        false
% 11.41/2.01  --soft_assumptions                      false
% 11.41/2.01  --soft_lemma_size                       3
% 11.41/2.01  --prop_impl_unit_size                   0
% 11.41/2.01  --prop_impl_unit                        []
% 11.41/2.01  --share_sel_clauses                     true
% 11.41/2.01  --reset_solvers                         false
% 11.41/2.01  --bc_imp_inh                            [conj_cone]
% 11.41/2.01  --conj_cone_tolerance                   3.
% 11.41/2.01  --extra_neg_conj                        none
% 11.41/2.01  --large_theory_mode                     true
% 11.41/2.01  --prolific_symb_bound                   200
% 11.41/2.01  --lt_threshold                          2000
% 11.41/2.01  --clause_weak_htbl                      true
% 11.41/2.01  --gc_record_bc_elim                     false
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing Options
% 11.41/2.01  
% 11.41/2.01  --preprocessing_flag                    true
% 11.41/2.01  --time_out_prep_mult                    0.1
% 11.41/2.01  --splitting_mode                        input
% 11.41/2.01  --splitting_grd                         true
% 11.41/2.01  --splitting_cvd                         false
% 11.41/2.01  --splitting_cvd_svl                     false
% 11.41/2.01  --splitting_nvd                         32
% 11.41/2.01  --sub_typing                            true
% 11.41/2.01  --prep_gs_sim                           true
% 11.41/2.01  --prep_unflatten                        true
% 11.41/2.01  --prep_res_sim                          true
% 11.41/2.01  --prep_upred                            true
% 11.41/2.01  --prep_sem_filter                       exhaustive
% 11.41/2.01  --prep_sem_filter_out                   false
% 11.41/2.01  --pred_elim                             true
% 11.41/2.01  --res_sim_input                         true
% 11.41/2.01  --eq_ax_congr_red                       true
% 11.41/2.01  --pure_diseq_elim                       true
% 11.41/2.01  --brand_transform                       false
% 11.41/2.01  --non_eq_to_eq                          false
% 11.41/2.01  --prep_def_merge                        true
% 11.41/2.01  --prep_def_merge_prop_impl              false
% 11.41/2.01  --prep_def_merge_mbd                    true
% 11.41/2.01  --prep_def_merge_tr_red                 false
% 11.41/2.01  --prep_def_merge_tr_cl                  false
% 11.41/2.01  --smt_preprocessing                     true
% 11.41/2.01  --smt_ac_axioms                         fast
% 11.41/2.01  --preprocessed_out                      false
% 11.41/2.01  --preprocessed_stats                    false
% 11.41/2.01  
% 11.41/2.01  ------ Abstraction refinement Options
% 11.41/2.01  
% 11.41/2.01  --abstr_ref                             []
% 11.41/2.01  --abstr_ref_prep                        false
% 11.41/2.01  --abstr_ref_until_sat                   false
% 11.41/2.01  --abstr_ref_sig_restrict                funpre
% 11.41/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/2.01  --abstr_ref_under                       []
% 11.41/2.01  
% 11.41/2.01  ------ SAT Options
% 11.41/2.01  
% 11.41/2.01  --sat_mode                              false
% 11.41/2.01  --sat_fm_restart_options                ""
% 11.41/2.01  --sat_gr_def                            false
% 11.41/2.01  --sat_epr_types                         true
% 11.41/2.01  --sat_non_cyclic_types                  false
% 11.41/2.01  --sat_finite_models                     false
% 11.41/2.01  --sat_fm_lemmas                         false
% 11.41/2.01  --sat_fm_prep                           false
% 11.41/2.01  --sat_fm_uc_incr                        true
% 11.41/2.01  --sat_out_model                         small
% 11.41/2.01  --sat_out_clauses                       false
% 11.41/2.01  
% 11.41/2.01  ------ QBF Options
% 11.41/2.01  
% 11.41/2.01  --qbf_mode                              false
% 11.41/2.01  --qbf_elim_univ                         false
% 11.41/2.01  --qbf_dom_inst                          none
% 11.41/2.01  --qbf_dom_pre_inst                      false
% 11.41/2.01  --qbf_sk_in                             false
% 11.41/2.01  --qbf_pred_elim                         true
% 11.41/2.01  --qbf_split                             512
% 11.41/2.01  
% 11.41/2.01  ------ BMC1 Options
% 11.41/2.01  
% 11.41/2.01  --bmc1_incremental                      false
% 11.41/2.01  --bmc1_axioms                           reachable_all
% 11.41/2.01  --bmc1_min_bound                        0
% 11.41/2.01  --bmc1_max_bound                        -1
% 11.41/2.01  --bmc1_max_bound_default                -1
% 11.41/2.01  --bmc1_symbol_reachability              true
% 11.41/2.01  --bmc1_property_lemmas                  false
% 11.41/2.01  --bmc1_k_induction                      false
% 11.41/2.01  --bmc1_non_equiv_states                 false
% 11.41/2.01  --bmc1_deadlock                         false
% 11.41/2.01  --bmc1_ucm                              false
% 11.41/2.01  --bmc1_add_unsat_core                   none
% 11.41/2.01  --bmc1_unsat_core_children              false
% 11.41/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/2.01  --bmc1_out_stat                         full
% 11.41/2.01  --bmc1_ground_init                      false
% 11.41/2.01  --bmc1_pre_inst_next_state              false
% 11.41/2.01  --bmc1_pre_inst_state                   false
% 11.41/2.01  --bmc1_pre_inst_reach_state             false
% 11.41/2.01  --bmc1_out_unsat_core                   false
% 11.41/2.01  --bmc1_aig_witness_out                  false
% 11.41/2.01  --bmc1_verbose                          false
% 11.41/2.01  --bmc1_dump_clauses_tptp                false
% 11.41/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.41/2.01  --bmc1_dump_file                        -
% 11.41/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.41/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.41/2.01  --bmc1_ucm_extend_mode                  1
% 11.41/2.01  --bmc1_ucm_init_mode                    2
% 11.41/2.01  --bmc1_ucm_cone_mode                    none
% 11.41/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.41/2.01  --bmc1_ucm_relax_model                  4
% 11.41/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.41/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/2.01  --bmc1_ucm_layered_model                none
% 11.41/2.01  --bmc1_ucm_max_lemma_size               10
% 11.41/2.01  
% 11.41/2.01  ------ AIG Options
% 11.41/2.01  
% 11.41/2.01  --aig_mode                              false
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation Options
% 11.41/2.01  
% 11.41/2.01  --instantiation_flag                    true
% 11.41/2.01  --inst_sos_flag                         false
% 11.41/2.01  --inst_sos_phase                        true
% 11.41/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel_side                     none
% 11.41/2.01  --inst_solver_per_active                1400
% 11.41/2.01  --inst_solver_calls_frac                1.
% 11.41/2.01  --inst_passive_queue_type               priority_queues
% 11.41/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/2.01  --inst_passive_queues_freq              [25;2]
% 11.41/2.01  --inst_dismatching                      true
% 11.41/2.01  --inst_eager_unprocessed_to_passive     true
% 11.41/2.01  --inst_prop_sim_given                   true
% 11.41/2.01  --inst_prop_sim_new                     false
% 11.41/2.01  --inst_subs_new                         false
% 11.41/2.01  --inst_eq_res_simp                      false
% 11.41/2.01  --inst_subs_given                       false
% 11.41/2.01  --inst_orphan_elimination               true
% 11.41/2.01  --inst_learning_loop_flag               true
% 11.41/2.01  --inst_learning_start                   3000
% 11.41/2.01  --inst_learning_factor                  2
% 11.41/2.01  --inst_start_prop_sim_after_learn       3
% 11.41/2.01  --inst_sel_renew                        solver
% 11.41/2.01  --inst_lit_activity_flag                true
% 11.41/2.01  --inst_restr_to_given                   false
% 11.41/2.01  --inst_activity_threshold               500
% 11.41/2.01  --inst_out_proof                        true
% 11.41/2.01  
% 11.41/2.01  ------ Resolution Options
% 11.41/2.01  
% 11.41/2.01  --resolution_flag                       false
% 11.41/2.01  --res_lit_sel                           adaptive
% 11.41/2.01  --res_lit_sel_side                      none
% 11.41/2.01  --res_ordering                          kbo
% 11.41/2.01  --res_to_prop_solver                    active
% 11.41/2.01  --res_prop_simpl_new                    false
% 11.41/2.01  --res_prop_simpl_given                  true
% 11.41/2.01  --res_passive_queue_type                priority_queues
% 11.41/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/2.01  --res_passive_queues_freq               [15;5]
% 11.41/2.01  --res_forward_subs                      full
% 11.41/2.01  --res_backward_subs                     full
% 11.41/2.01  --res_forward_subs_resolution           true
% 11.41/2.01  --res_backward_subs_resolution          true
% 11.41/2.01  --res_orphan_elimination                true
% 11.41/2.01  --res_time_limit                        2.
% 11.41/2.01  --res_out_proof                         true
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Options
% 11.41/2.01  
% 11.41/2.01  --superposition_flag                    true
% 11.41/2.01  --sup_passive_queue_type                priority_queues
% 11.41/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.41/2.01  --demod_completeness_check              fast
% 11.41/2.01  --demod_use_ground                      true
% 11.41/2.01  --sup_to_prop_solver                    passive
% 11.41/2.01  --sup_prop_simpl_new                    true
% 11.41/2.01  --sup_prop_simpl_given                  true
% 11.41/2.01  --sup_fun_splitting                     false
% 11.41/2.01  --sup_smt_interval                      50000
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Simplification Setup
% 11.41/2.01  
% 11.41/2.01  --sup_indices_passive                   []
% 11.41/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_full_bw                           [BwDemod]
% 11.41/2.01  --sup_immed_triv                        [TrivRules]
% 11.41/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_immed_bw_main                     []
% 11.41/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/2.01  
% 11.41/2.01  ------ Combination Options
% 11.41/2.01  
% 11.41/2.01  --comb_res_mult                         3
% 11.41/2.01  --comb_sup_mult                         2
% 11.41/2.01  --comb_inst_mult                        10
% 11.41/2.01  
% 11.41/2.01  ------ Debug Options
% 11.41/2.01  
% 11.41/2.01  --dbg_backtrace                         false
% 11.41/2.01  --dbg_dump_prop_clauses                 false
% 11.41/2.01  --dbg_dump_prop_clauses_file            -
% 11.41/2.01  --dbg_out_stat                          false
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  ------ Proving...
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  % SZS status Theorem for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  fof(f15,conjecture,(
% 11.41/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f16,negated_conjecture,(
% 11.41/2.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 11.41/2.01    inference(negated_conjecture,[],[f15])).
% 11.41/2.01  
% 11.41/2.01  fof(f36,plain,(
% 11.41/2.01    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.41/2.01    inference(ennf_transformation,[],[f16])).
% 11.41/2.01  
% 11.41/2.01  fof(f37,plain,(
% 11.41/2.01    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.41/2.01    inference(flattening,[],[f36])).
% 11.41/2.01  
% 11.41/2.01  fof(f43,plain,(
% 11.41/2.01    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 11.41/2.01    introduced(choice_axiom,[])).
% 11.41/2.01  
% 11.41/2.01  fof(f42,plain,(
% 11.41/2.01    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.41/2.01    introduced(choice_axiom,[])).
% 11.41/2.01  
% 11.41/2.01  fof(f44,plain,(
% 11.41/2.01    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.41/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f43,f42])).
% 11.41/2.01  
% 11.41/2.01  fof(f74,plain,(
% 11.41/2.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f9,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f26,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(ennf_transformation,[],[f9])).
% 11.41/2.01  
% 11.41/2.01  fof(f56,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f26])).
% 11.41/2.01  
% 11.41/2.01  fof(f12,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f30,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(ennf_transformation,[],[f12])).
% 11.41/2.01  
% 11.41/2.01  fof(f31,plain,(
% 11.41/2.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(flattening,[],[f30])).
% 11.41/2.01  
% 11.41/2.01  fof(f41,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(nnf_transformation,[],[f31])).
% 11.41/2.01  
% 11.41/2.01  fof(f59,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f41])).
% 11.41/2.01  
% 11.41/2.01  fof(f73,plain,(
% 11.41/2.01    v1_funct_2(sK4,sK1,sK2)),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f77,plain,(
% 11.41/2.01    k1_xboole_0 != sK2),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f14,axiom,(
% 11.41/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f34,plain,(
% 11.41/2.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.41/2.01    inference(ennf_transformation,[],[f14])).
% 11.41/2.01  
% 11.41/2.01  fof(f35,plain,(
% 11.41/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.41/2.01    inference(flattening,[],[f34])).
% 11.41/2.01  
% 11.41/2.01  fof(f68,plain,(
% 11.41/2.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f35])).
% 11.41/2.01  
% 11.41/2.01  fof(f72,plain,(
% 11.41/2.01    v1_funct_1(sK4)),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f6,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f22,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(ennf_transformation,[],[f6])).
% 11.41/2.01  
% 11.41/2.01  fof(f53,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f22])).
% 11.41/2.01  
% 11.41/2.01  fof(f1,axiom,(
% 11.41/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f38,plain,(
% 11.41/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/2.01    inference(nnf_transformation,[],[f1])).
% 11.41/2.01  
% 11.41/2.01  fof(f39,plain,(
% 11.41/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/2.01    inference(flattening,[],[f38])).
% 11.41/2.01  
% 11.41/2.01  fof(f46,plain,(
% 11.41/2.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.41/2.01    inference(cnf_transformation,[],[f39])).
% 11.41/2.01  
% 11.41/2.01  fof(f79,plain,(
% 11.41/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.41/2.01    inference(equality_resolution,[],[f46])).
% 11.41/2.01  
% 11.41/2.01  fof(f11,axiom,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f28,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.41/2.01    inference(ennf_transformation,[],[f11])).
% 11.41/2.01  
% 11.41/2.01  fof(f29,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(flattening,[],[f28])).
% 11.41/2.01  
% 11.41/2.01  fof(f58,plain,(
% 11.41/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f29])).
% 11.41/2.01  
% 11.41/2.01  fof(f8,axiom,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f24,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.41/2.01    inference(ennf_transformation,[],[f8])).
% 11.41/2.01  
% 11.41/2.01  fof(f25,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(flattening,[],[f24])).
% 11.41/2.01  
% 11.41/2.01  fof(f55,plain,(
% 11.41/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f25])).
% 11.41/2.01  
% 11.41/2.01  fof(f69,plain,(
% 11.41/2.01    v1_funct_1(sK3)),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f71,plain,(
% 11.41/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f78,plain,(
% 11.41/2.01    k2_relset_1(sK0,sK1,sK3) != sK1),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f7,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f17,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.41/2.01    inference(pure_predicate_removal,[],[f7])).
% 11.41/2.01  
% 11.41/2.01  fof(f23,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(ennf_transformation,[],[f17])).
% 11.41/2.01  
% 11.41/2.01  fof(f54,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f23])).
% 11.41/2.01  
% 11.41/2.01  fof(f3,axiom,(
% 11.41/2.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f19,plain,(
% 11.41/2.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.41/2.01    inference(ennf_transformation,[],[f3])).
% 11.41/2.01  
% 11.41/2.01  fof(f40,plain,(
% 11.41/2.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.41/2.01    inference(nnf_transformation,[],[f19])).
% 11.41/2.01  
% 11.41/2.01  fof(f49,plain,(
% 11.41/2.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f40])).
% 11.41/2.01  
% 11.41/2.01  fof(f10,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f27,plain,(
% 11.41/2.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/2.01    inference(ennf_transformation,[],[f10])).
% 11.41/2.01  
% 11.41/2.01  fof(f57,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f27])).
% 11.41/2.01  
% 11.41/2.01  fof(f47,plain,(
% 11.41/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f39])).
% 11.41/2.01  
% 11.41/2.01  fof(f13,axiom,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f32,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.41/2.01    inference(ennf_transformation,[],[f13])).
% 11.41/2.01  
% 11.41/2.01  fof(f33,plain,(
% 11.41/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.41/2.01    inference(flattening,[],[f32])).
% 11.41/2.01  
% 11.41/2.01  fof(f65,plain,(
% 11.41/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f33])).
% 11.41/2.01  
% 11.41/2.01  fof(f75,plain,(
% 11.41/2.01    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  fof(f5,axiom,(
% 11.41/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 11.41/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f20,plain,(
% 11.41/2.01    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.41/2.01    inference(ennf_transformation,[],[f5])).
% 11.41/2.01  
% 11.41/2.01  fof(f21,plain,(
% 11.41/2.01    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.41/2.01    inference(flattening,[],[f20])).
% 11.41/2.01  
% 11.41/2.01  fof(f52,plain,(
% 11.41/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f21])).
% 11.41/2.01  
% 11.41/2.01  fof(f76,plain,(
% 11.41/2.01    v2_funct_1(sK4)),
% 11.41/2.01    inference(cnf_transformation,[],[f44])).
% 11.41/2.01  
% 11.41/2.01  cnf(c_28,negated_conjecture,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.41/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1197,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_11,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1202,plain,
% 11.41/2.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2346,plain,
% 11.41/2.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1197,c_1202]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_19,plain,
% 11.41/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.41/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.41/2.01      | k1_xboole_0 = X2 ),
% 11.41/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_29,negated_conjecture,
% 11.41/2.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 11.41/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_540,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.41/2.01      | sK4 != X0
% 11.41/2.01      | sK2 != X2
% 11.41/2.01      | sK1 != X1
% 11.41/2.01      | k1_xboole_0 = X2 ),
% 11.41/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_541,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.41/2.01      | k1_relset_1(sK1,sK2,sK4) = sK1
% 11.41/2.01      | k1_xboole_0 = sK2 ),
% 11.41/2.01      inference(unflattening,[status(thm)],[c_540]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_25,negated_conjecture,
% 11.41/2.01      ( k1_xboole_0 != sK2 ),
% 11.41/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_543,plain,
% 11.41/2.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_541,c_28,c_25]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2351,plain,
% 11.41/2.01      ( k1_relat_1(sK4) = sK1 ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_2346,c_543]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_21,plain,
% 11.41/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 11.41/2.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1198,plain,
% 11.41/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2640,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 11.41/2.01      | v1_funct_1(sK4) != iProver_top
% 11.41/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_2351,c_1198]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_30,negated_conjecture,
% 11.41/2.01      ( v1_funct_1(sK4) ),
% 11.41/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_37,plain,
% 11.41/2.01      ( v1_funct_1(sK4) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_39,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | v1_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1412,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.41/2.01      | v1_relat_1(sK4) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1413,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.41/2.01      | v1_relat_1(sK4) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3190,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_2640,c_37,c_39,c_1413]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1,plain,
% 11.41/2.01      ( r1_tarski(X0,X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1207,plain,
% 11.41/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_13,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.41/2.01      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1200,plain,
% 11.41/2.01      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.41/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.41/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3415,plain,
% 11.41/2.01      ( k4_relset_1(X0,X1,sK1,X2,X3,sK4) = k5_relat_1(X3,sK4)
% 11.41/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(sK4),X2) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_3190,c_1200]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8748,plain,
% 11.41/2.01      ( k4_relset_1(sK1,sK2,sK1,X0,sK4,sK4) = k5_relat_1(sK4,sK4)
% 11.41/2.01      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1197,c_3415]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8868,plain,
% 11.41/2.01      ( k4_relset_1(sK1,sK2,sK1,k2_relat_1(sK4),sK4,sK4) = k5_relat_1(sK4,sK4) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1207,c_8748]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_10,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.41/2.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 11.41/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1203,plain,
% 11.41/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.41/2.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8886,plain,
% 11.41/2.01      ( m1_subset_1(k5_relat_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top
% 11.41/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
% 11.41/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_8868,c_1203]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_33,negated_conjecture,
% 11.41/2.01      ( v1_funct_1(sK3) ),
% 11.41/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_34,plain,
% 11.41/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_31,negated_conjecture,
% 11.41/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.41/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_36,plain,
% 11.41/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_24,negated_conjecture,
% 11.41/2.01      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 11.41/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1415,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.41/2.01      | v1_relat_1(sK3) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1416,plain,
% 11.41/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.41/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_9,plain,
% 11.41/2.01      ( v5_relat_1(X0,X1)
% 11.41/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.41/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5,plain,
% 11.41/2.01      ( ~ v5_relat_1(X0,X1)
% 11.41/2.01      | r1_tarski(k2_relat_1(X0),X1)
% 11.41/2.01      | ~ v1_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_367,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | r1_tarski(k2_relat_1(X0),X2)
% 11.41/2.01      | ~ v1_relat_1(X0) ),
% 11.41/2.01      inference(resolution,[status(thm)],[c_9,c_5]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_371,plain,
% 11.41/2.01      ( r1_tarski(k2_relat_1(X0),X2)
% 11.41/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_367,c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_372,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.41/2.01      inference(renaming,[status(thm)],[c_371]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1434,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.41/2.01      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_372]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1435,plain,
% 11.41/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_12,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1485,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.41/2.01      | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_0,plain,
% 11.41/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.41/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1631,plain,
% 11.41/2.01      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2578,plain,
% 11.41/2.01      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 11.41/2.01      | ~ r1_tarski(sK1,k2_relat_1(sK3))
% 11.41/2.01      | sK1 = k2_relat_1(sK3) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1631]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2579,plain,
% 11.41/2.01      ( sK1 = k2_relat_1(sK3)
% 11.41/2.01      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 11.41/2.01      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_2578]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_762,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1467,plain,
% 11.41/2.01      ( k2_relset_1(sK0,sK1,sK3) != X0
% 11.41/2.01      | k2_relset_1(sK0,sK1,sK3) = sK1
% 11.41/2.01      | sK1 != X0 ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_762]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3851,plain,
% 11.41/2.01      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 11.41/2.01      | k2_relset_1(sK0,sK1,sK3) = sK1
% 11.41/2.01      | sK1 != k2_relat_1(sK3) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1467]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1192,plain,
% 11.41/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5638,plain,
% 11.41/2.01      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1197,c_1192]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1208,plain,
% 11.41/2.01      ( X0 = X1
% 11.41/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.41/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5670,plain,
% 11.41/2.01      ( k2_relat_1(sK4) = sK2
% 11.41/2.01      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_5638,c_1208]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1195,plain,
% 11.41/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3413,plain,
% 11.41/2.01      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1197,c_1200]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3976,plain,
% 11.41/2.01      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1195,c_3413]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_4177,plain,
% 11.41/2.01      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 11.41/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.41/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_3976,c_1203]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5976,plain,
% 11.41/2.01      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_4177,c_36,c_39]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1201,plain,
% 11.41/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5987,plain,
% 11.41/2.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_5976,c_1201]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_20,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_funct_1(X3)
% 11.41/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1199,plain,
% 11.41/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.41/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.41/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/2.01      | v1_funct_1(X5) != iProver_top
% 11.41/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3771,plain,
% 11.41/2.01      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/2.01      | v1_funct_1(X2) != iProver_top
% 11.41/2.01      | v1_funct_1(sK4) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1197,c_1199]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_4540,plain,
% 11.41/2.01      ( v1_funct_1(X2) != iProver_top
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/2.01      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_3771,c_37]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_4541,plain,
% 11.41/2.01      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 11.41/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.41/2.01      inference(renaming,[status(thm)],[c_4540]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_4552,plain,
% 11.41/2.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.41/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1195,c_4541]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1537,plain,
% 11.41/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_funct_1(sK4)
% 11.41/2.01      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_20]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1772,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.41/2.01      | ~ v1_funct_1(sK4)
% 11.41/2.01      | ~ v1_funct_1(sK3)
% 11.41/2.01      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1537]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2095,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.41/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/2.01      | ~ v1_funct_1(sK4)
% 11.41/2.01      | ~ v1_funct_1(sK3)
% 11.41/2.01      | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1772]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_3042,plain,
% 11.41/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.41/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.41/2.01      | ~ v1_funct_1(sK4)
% 11.41/2.01      | ~ v1_funct_1(sK3)
% 11.41/2.01      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_2095]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5126,plain,
% 11.41/2.01      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_4552,c_33,c_31,c_30,c_28,c_3042]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_27,negated_conjecture,
% 11.41/2.01      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 11.41/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5129,plain,
% 11.41/2.01      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_5126,c_27]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_6009,plain,
% 11.41/2.01      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_5987,c_5129]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_7,plain,
% 11.41/2.01      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 11.41/2.01      | ~ v1_funct_1(X1)
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v2_funct_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X1)
% 11.41/2.01      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_26,negated_conjecture,
% 11.41/2.01      ( v2_funct_1(sK4) ),
% 11.41/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_334,plain,
% 11.41/2.01      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 11.41/2.01      | ~ v1_funct_1(X1)
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X1)
% 11.41/2.01      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
% 11.41/2.01      | sK4 != X0 ),
% 11.41/2.01      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_335,plain,
% 11.41/2.01      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_funct_1(sK4)
% 11.41/2.01      | ~ v1_relat_1(X0)
% 11.41/2.01      | ~ v1_relat_1(sK4)
% 11.41/2.01      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 11.41/2.01      inference(unflattening,[status(thm)],[c_334]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_339,plain,
% 11.41/2.01      ( ~ v1_funct_1(X0)
% 11.41/2.01      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 11.41/2.01      | ~ v1_relat_1(X0)
% 11.41/2.01      | ~ v1_relat_1(sK4)
% 11.41/2.01      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_335,c_30]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_340,plain,
% 11.41/2.01      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 11.41/2.01      | ~ v1_funct_1(X0)
% 11.41/2.01      | ~ v1_relat_1(X0)
% 11.41/2.01      | ~ v1_relat_1(sK4)
% 11.41/2.01      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 11.41/2.01      inference(renaming,[status(thm)],[c_339]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1193,plain,
% 11.41/2.01      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 11.41/2.01      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_336,plain,
% 11.41/2.01      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 11.41/2.01      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | v1_funct_1(sK4) != iProver_top
% 11.41/2.01      | v1_relat_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2114,plain,
% 11.41/2.01      ( v1_relat_1(X0) != iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 11.41/2.01      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_1193,c_37,c_39,c_336,c_1413]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2115,plain,
% 11.41/2.01      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 11.41/2.01      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.41/2.01      inference(renaming,[status(thm)],[c_2114]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_2636,plain,
% 11.41/2.01      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 11.41/2.01      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 11.41/2.01      | v1_funct_1(X0) != iProver_top
% 11.41/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_2351,c_2115]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_6048,plain,
% 11.41/2.01      ( k2_relat_1(sK4) != sK2
% 11.41/2.01      | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
% 11.41/2.01      | v1_funct_1(sK3) != iProver_top
% 11.41/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_6009,c_2636]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8749,plain,
% 11.41/2.01      ( k4_relset_1(sK0,sK1,sK1,X0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.41/2.01      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1195,c_3415]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8891,plain,
% 11.41/2.01      ( k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1207,c_8749]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5636,plain,
% 11.41/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_1203,c_1192]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_26441,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
% 11.41/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.41/2.01      | r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_8891,c_5636]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_26835,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
% 11.41/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.41/2.01      | r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_26441,c_6009]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_27197,plain,
% 11.41/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top ),
% 11.41/2.01      inference(global_propositional_subsumption,
% 11.41/2.01                [status(thm)],
% 11.41/2.01                [c_8886,c_34,c_31,c_36,c_24,c_1416,c_1435,c_1485,c_2579,
% 11.41/2.01                 c_3851,c_5670,c_6048,c_26835]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_27202,plain,
% 11.41/2.01      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_3190,c_27197]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1657,plain,
% 11.41/2.01      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1660,plain,
% 11.41/2.01      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top ),
% 11.41/2.01      inference(predicate_to_equality,[status(thm)],[c_1657]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(contradiction,plain,
% 11.41/2.01      ( $false ),
% 11.41/2.01      inference(minisat,[status(thm)],[c_27202,c_1660]) ).
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  ------                               Statistics
% 11.41/2.01  
% 11.41/2.01  ------ General
% 11.41/2.01  
% 11.41/2.01  abstr_ref_over_cycles:                  0
% 11.41/2.01  abstr_ref_under_cycles:                 0
% 11.41/2.01  gc_basic_clause_elim:                   0
% 11.41/2.01  forced_gc_time:                         0
% 11.41/2.01  parsing_time:                           0.011
% 11.41/2.01  unif_index_cands_time:                  0.
% 11.41/2.01  unif_index_add_time:                    0.
% 11.41/2.01  orderings_time:                         0.
% 11.41/2.01  out_proof_time:                         0.023
% 11.41/2.01  total_time:                             1.218
% 11.41/2.01  num_of_symbols:                         53
% 11.41/2.01  num_of_terms:                           26529
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing
% 11.41/2.01  
% 11.41/2.01  num_of_splits:                          0
% 11.41/2.01  num_of_split_atoms:                     0
% 11.41/2.01  num_of_reused_defs:                     0
% 11.41/2.01  num_eq_ax_congr_red:                    27
% 11.41/2.01  num_of_sem_filtered_clauses:            1
% 11.41/2.01  num_of_subtypes:                        0
% 11.41/2.01  monotx_restored_types:                  0
% 11.41/2.01  sat_num_of_epr_types:                   0
% 11.41/2.01  sat_num_of_non_cyclic_types:            0
% 11.41/2.01  sat_guarded_non_collapsed_types:        0
% 11.41/2.01  num_pure_diseq_elim:                    0
% 11.41/2.01  simp_replaced_by:                       0
% 11.41/2.01  res_preprocessed:                       148
% 11.41/2.01  prep_upred:                             0
% 11.41/2.01  prep_unflattend:                        43
% 11.41/2.01  smt_new_axioms:                         0
% 11.41/2.01  pred_elim_cands:                        4
% 11.41/2.01  pred_elim:                              3
% 11.41/2.01  pred_elim_cl:                           3
% 11.41/2.01  pred_elim_cycles:                       5
% 11.41/2.01  merged_defs:                            0
% 11.41/2.01  merged_defs_ncl:                        0
% 11.41/2.01  bin_hyper_res:                          0
% 11.41/2.01  prep_cycles:                            4
% 11.41/2.01  pred_elim_time:                         0.007
% 11.41/2.01  splitting_time:                         0.
% 11.41/2.01  sem_filter_time:                        0.
% 11.41/2.01  monotx_time:                            0.001
% 11.41/2.01  subtype_inf_time:                       0.
% 11.41/2.01  
% 11.41/2.01  ------ Problem properties
% 11.41/2.01  
% 11.41/2.01  clauses:                                29
% 11.41/2.01  conjectures:                            7
% 11.41/2.01  epr:                                    5
% 11.41/2.01  horn:                                   24
% 11.41/2.01  ground:                                 13
% 11.41/2.01  unary:                                  10
% 11.41/2.01  binary:                                 5
% 11.41/2.01  lits:                                   74
% 11.41/2.01  lits_eq:                                28
% 11.41/2.01  fd_pure:                                0
% 11.41/2.01  fd_pseudo:                              0
% 11.41/2.01  fd_cond:                                2
% 11.41/2.01  fd_pseudo_cond:                         1
% 11.41/2.01  ac_symbols:                             0
% 11.41/2.01  
% 11.41/2.01  ------ Propositional Solver
% 11.41/2.01  
% 11.41/2.01  prop_solver_calls:                      31
% 11.41/2.01  prop_fast_solver_calls:                 1637
% 11.41/2.01  smt_solver_calls:                       0
% 11.41/2.01  smt_fast_solver_calls:                  0
% 11.41/2.01  prop_num_of_clauses:                    10466
% 11.41/2.01  prop_preprocess_simplified:             14674
% 11.41/2.01  prop_fo_subsumed:                       110
% 11.41/2.01  prop_solver_time:                       0.
% 11.41/2.01  smt_solver_time:                        0.
% 11.41/2.01  smt_fast_solver_time:                   0.
% 11.41/2.01  prop_fast_solver_time:                  0.
% 11.41/2.01  prop_unsat_core_time:                   0.002
% 11.41/2.01  
% 11.41/2.01  ------ QBF
% 11.41/2.01  
% 11.41/2.01  qbf_q_res:                              0
% 11.41/2.01  qbf_num_tautologies:                    0
% 11.41/2.01  qbf_prep_cycles:                        0
% 11.41/2.01  
% 11.41/2.01  ------ BMC1
% 11.41/2.01  
% 11.41/2.01  bmc1_current_bound:                     -1
% 11.41/2.01  bmc1_last_solved_bound:                 -1
% 11.41/2.01  bmc1_unsat_core_size:                   -1
% 11.41/2.01  bmc1_unsat_core_parents_size:           -1
% 11.41/2.01  bmc1_merge_next_fun:                    0
% 11.41/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation
% 11.41/2.01  
% 11.41/2.01  inst_num_of_clauses:                    2778
% 11.41/2.01  inst_num_in_passive:                    832
% 11.41/2.01  inst_num_in_active:                     1561
% 11.41/2.01  inst_num_in_unprocessed:                385
% 11.41/2.01  inst_num_of_loops:                      1630
% 11.41/2.01  inst_num_of_learning_restarts:          0
% 11.41/2.01  inst_num_moves_active_passive:          65
% 11.41/2.01  inst_lit_activity:                      0
% 11.41/2.01  inst_lit_activity_moves:                1
% 11.41/2.01  inst_num_tautologies:                   0
% 11.41/2.01  inst_num_prop_implied:                  0
% 11.41/2.01  inst_num_existing_simplified:           0
% 11.41/2.01  inst_num_eq_res_simplified:             0
% 11.41/2.01  inst_num_child_elim:                    0
% 11.41/2.01  inst_num_of_dismatching_blockings:      1100
% 11.41/2.01  inst_num_of_non_proper_insts:           2694
% 11.41/2.01  inst_num_of_duplicates:                 0
% 11.41/2.01  inst_inst_num_from_inst_to_res:         0
% 11.41/2.01  inst_dismatching_checking_time:         0.
% 11.41/2.01  
% 11.41/2.01  ------ Resolution
% 11.41/2.01  
% 11.41/2.01  res_num_of_clauses:                     0
% 11.41/2.01  res_num_in_passive:                     0
% 11.41/2.01  res_num_in_active:                      0
% 11.41/2.01  res_num_of_loops:                       152
% 11.41/2.01  res_forward_subset_subsumed:            225
% 11.41/2.01  res_backward_subset_subsumed:           0
% 11.41/2.01  res_forward_subsumed:                   0
% 11.41/2.01  res_backward_subsumed:                  0
% 11.41/2.01  res_forward_subsumption_resolution:     3
% 11.41/2.01  res_backward_subsumption_resolution:    0
% 11.41/2.01  res_clause_to_clause_subsumption:       2702
% 11.41/2.01  res_orphan_elimination:                 0
% 11.41/2.01  res_tautology_del:                      230
% 11.41/2.01  res_num_eq_res_simplified:              0
% 11.41/2.01  res_num_sel_changes:                    0
% 11.41/2.01  res_moves_from_active_to_pass:          0
% 11.41/2.01  
% 11.41/2.01  ------ Superposition
% 11.41/2.01  
% 11.41/2.01  sup_time_total:                         0.
% 11.41/2.01  sup_time_generating:                    0.
% 11.41/2.01  sup_time_sim_full:                      0.
% 11.41/2.01  sup_time_sim_immed:                     0.
% 11.41/2.01  
% 11.41/2.01  sup_num_of_clauses:                     1338
% 11.41/2.01  sup_num_in_active:                      322
% 11.41/2.01  sup_num_in_passive:                     1016
% 11.41/2.01  sup_num_of_loops:                       324
% 11.41/2.01  sup_fw_superposition:                   999
% 11.41/2.01  sup_bw_superposition:                   576
% 11.41/2.01  sup_immediate_simplified:               521
% 11.41/2.01  sup_given_eliminated:                   0
% 11.41/2.01  comparisons_done:                       0
% 11.41/2.01  comparisons_avoided:                    16
% 11.41/2.01  
% 11.41/2.01  ------ Simplifications
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  sim_fw_subset_subsumed:                 91
% 11.41/2.01  sim_bw_subset_subsumed:                 12
% 11.41/2.01  sim_fw_subsumed:                        34
% 11.41/2.01  sim_bw_subsumed:                        3
% 11.41/2.01  sim_fw_subsumption_res:                 0
% 11.41/2.01  sim_bw_subsumption_res:                 0
% 11.41/2.01  sim_tautology_del:                      5
% 11.41/2.01  sim_eq_tautology_del:                   56
% 11.41/2.01  sim_eq_res_simp:                        0
% 11.41/2.01  sim_fw_demodulated:                     0
% 11.41/2.01  sim_bw_demodulated:                     4
% 11.41/2.01  sim_light_normalised:                   433
% 11.41/2.01  sim_joinable_taut:                      0
% 11.41/2.01  sim_joinable_simp:                      0
% 11.41/2.01  sim_ac_normalised:                      0
% 11.41/2.01  sim_smt_subsumption:                    0
% 11.41/2.01  
%------------------------------------------------------------------------------
