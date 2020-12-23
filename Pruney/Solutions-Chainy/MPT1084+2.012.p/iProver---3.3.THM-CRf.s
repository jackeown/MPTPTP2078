%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:33 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  121 (1086 expanded)
%              Number of clauses        :   67 ( 275 expanded)
%              Number of leaves         :   12 ( 269 expanded)
%              Depth                    :   27
%              Number of atoms          :  495 (6436 expanded)
%              Number of equality atoms :  200 (1465 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
     => ( ~ r2_funct_2(X0,X0,sK2,k6_partfun1(X0))
        & ! [X2] :
            ( k3_funct_2(X0,X0,sK2,X2) = X2
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1))
          & ! [X2] :
              ( k3_funct_2(sK1,sK1,X1,X2) = X2
              | ~ m1_subset_1(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X1,sK1,sK1)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))
    & ! [X2] :
        ( k3_funct_2(sK1,sK1,sK2,X2) = X2
        | ~ m1_subset_1(X2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f32,f31])).

fof(f51,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f60,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2] :
      ( k3_funct_2(sK1,sK1,sK2,X2) = X2
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f47])).

fof(f54,plain,(
    ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f59,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK2 != X2
    | sK1 != X1
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_250,c_19,c_18,c_16])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_299,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_300,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_435,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_300])).

cnf(c_436,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_440,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_16,c_438])).

cnf(c_522,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_440])).

cnf(c_523,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | v1_xboole_0(k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_735,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_523])).

cnf(c_736,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_1722,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_737,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_662,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_663,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_1891,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_663])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_270,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_18,c_16])).

cnf(c_1892,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1891,c_270])).

cnf(c_2097,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1722,c_737,c_1892])).

cnf(c_2098,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2097])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_751,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,X0) = X0
    | sK0(k1_relat_1(sK2),sK2) != X0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_523])).

cnf(c_752,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_1721,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_753,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK1
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_2034,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1721,c_753,c_1892])).

cnf(c_2035,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2034])).

cnf(c_2038,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2035,c_1892])).

cnf(c_1735,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,negated_conjecture,
    ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_228,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_partfun1(sK1) != X0
    | sK2 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_229,plain,
    ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | sK2 != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_275,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k6_partfun1(sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_229])).

cnf(c_356,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_275])).

cnf(c_645,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != X1
    | k6_partfun1(sK1) != X0
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_356])).

cnf(c_646,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_xboole_0(k6_partfun1(sK1))
    | k6_partfun1(sK1) != sK2 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_767,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k6_partfun1(sK1) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_356])).

cnf(c_1013,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_767])).

cnf(c_1020,plain,
    ( k6_partfun1(sK1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_1013])).

cnf(c_2042,plain,
    ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2038,c_1735,c_1020])).

cnf(c_2101,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2098,c_1892,c_2042])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_312,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_partfun1(k1_relat_1(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_313,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_313])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_425,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_427,plain,
    ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_16,c_425])).

cnf(c_1943,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2)
    | k6_partfun1(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_427,c_1892])).

cnf(c_1946,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1943,c_1020])).

cnf(c_2105,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2101,c_1735,c_1020,c_1946])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.48/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.48/1.01  
% 1.48/1.01  ------  iProver source info
% 1.48/1.01  
% 1.48/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.48/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.48/1.01  git: non_committed_changes: false
% 1.48/1.01  git: last_make_outside_of_git: false
% 1.48/1.01  
% 1.48/1.01  ------ 
% 1.48/1.01  
% 1.48/1.01  ------ Input Options
% 1.48/1.01  
% 1.48/1.01  --out_options                           all
% 1.48/1.01  --tptp_safe_out                         true
% 1.48/1.01  --problem_path                          ""
% 1.48/1.01  --include_path                          ""
% 1.48/1.01  --clausifier                            res/vclausify_rel
% 1.48/1.01  --clausifier_options                    --mode clausify
% 1.48/1.01  --stdin                                 false
% 1.48/1.01  --stats_out                             all
% 1.48/1.01  
% 1.48/1.01  ------ General Options
% 1.48/1.01  
% 1.48/1.01  --fof                                   false
% 1.48/1.01  --time_out_real                         305.
% 1.48/1.01  --time_out_virtual                      -1.
% 1.48/1.01  --symbol_type_check                     false
% 1.48/1.01  --clausify_out                          false
% 1.48/1.01  --sig_cnt_out                           false
% 1.48/1.01  --trig_cnt_out                          false
% 1.48/1.01  --trig_cnt_out_tolerance                1.
% 1.48/1.01  --trig_cnt_out_sk_spl                   false
% 1.48/1.01  --abstr_cl_out                          false
% 1.48/1.01  
% 1.48/1.01  ------ Global Options
% 1.48/1.01  
% 1.48/1.01  --schedule                              default
% 1.48/1.01  --add_important_lit                     false
% 1.48/1.01  --prop_solver_per_cl                    1000
% 1.48/1.01  --min_unsat_core                        false
% 1.48/1.01  --soft_assumptions                      false
% 1.48/1.01  --soft_lemma_size                       3
% 1.48/1.01  --prop_impl_unit_size                   0
% 1.48/1.01  --prop_impl_unit                        []
% 1.48/1.01  --share_sel_clauses                     true
% 1.48/1.01  --reset_solvers                         false
% 1.48/1.01  --bc_imp_inh                            [conj_cone]
% 1.48/1.01  --conj_cone_tolerance                   3.
% 1.48/1.01  --extra_neg_conj                        none
% 1.48/1.01  --large_theory_mode                     true
% 1.48/1.01  --prolific_symb_bound                   200
% 1.48/1.01  --lt_threshold                          2000
% 1.48/1.01  --clause_weak_htbl                      true
% 1.48/1.01  --gc_record_bc_elim                     false
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing Options
% 1.48/1.01  
% 1.48/1.01  --preprocessing_flag                    true
% 1.48/1.01  --time_out_prep_mult                    0.1
% 1.48/1.01  --splitting_mode                        input
% 1.48/1.01  --splitting_grd                         true
% 1.48/1.01  --splitting_cvd                         false
% 1.48/1.01  --splitting_cvd_svl                     false
% 1.48/1.01  --splitting_nvd                         32
% 1.48/1.01  --sub_typing                            true
% 1.48/1.01  --prep_gs_sim                           true
% 1.48/1.01  --prep_unflatten                        true
% 1.48/1.01  --prep_res_sim                          true
% 1.48/1.01  --prep_upred                            true
% 1.48/1.01  --prep_sem_filter                       exhaustive
% 1.48/1.01  --prep_sem_filter_out                   false
% 1.48/1.01  --pred_elim                             true
% 1.48/1.01  --res_sim_input                         true
% 1.48/1.01  --eq_ax_congr_red                       true
% 1.48/1.01  --pure_diseq_elim                       true
% 1.48/1.01  --brand_transform                       false
% 1.48/1.01  --non_eq_to_eq                          false
% 1.48/1.01  --prep_def_merge                        true
% 1.48/1.01  --prep_def_merge_prop_impl              false
% 1.48/1.01  --prep_def_merge_mbd                    true
% 1.48/1.01  --prep_def_merge_tr_red                 false
% 1.48/1.01  --prep_def_merge_tr_cl                  false
% 1.48/1.01  --smt_preprocessing                     true
% 1.48/1.01  --smt_ac_axioms                         fast
% 1.48/1.01  --preprocessed_out                      false
% 1.48/1.01  --preprocessed_stats                    false
% 1.48/1.01  
% 1.48/1.01  ------ Abstraction refinement Options
% 1.48/1.01  
% 1.48/1.01  --abstr_ref                             []
% 1.48/1.01  --abstr_ref_prep                        false
% 1.48/1.01  --abstr_ref_until_sat                   false
% 1.48/1.01  --abstr_ref_sig_restrict                funpre
% 1.48/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.01  --abstr_ref_under                       []
% 1.48/1.01  
% 1.48/1.01  ------ SAT Options
% 1.48/1.01  
% 1.48/1.01  --sat_mode                              false
% 1.48/1.01  --sat_fm_restart_options                ""
% 1.48/1.01  --sat_gr_def                            false
% 1.48/1.01  --sat_epr_types                         true
% 1.48/1.01  --sat_non_cyclic_types                  false
% 1.48/1.01  --sat_finite_models                     false
% 1.48/1.01  --sat_fm_lemmas                         false
% 1.48/1.01  --sat_fm_prep                           false
% 1.48/1.01  --sat_fm_uc_incr                        true
% 1.48/1.01  --sat_out_model                         small
% 1.48/1.01  --sat_out_clauses                       false
% 1.48/1.01  
% 1.48/1.01  ------ QBF Options
% 1.48/1.01  
% 1.48/1.01  --qbf_mode                              false
% 1.48/1.01  --qbf_elim_univ                         false
% 1.48/1.01  --qbf_dom_inst                          none
% 1.48/1.01  --qbf_dom_pre_inst                      false
% 1.48/1.01  --qbf_sk_in                             false
% 1.48/1.01  --qbf_pred_elim                         true
% 1.48/1.01  --qbf_split                             512
% 1.48/1.01  
% 1.48/1.01  ------ BMC1 Options
% 1.48/1.01  
% 1.48/1.01  --bmc1_incremental                      false
% 1.48/1.01  --bmc1_axioms                           reachable_all
% 1.48/1.01  --bmc1_min_bound                        0
% 1.48/1.01  --bmc1_max_bound                        -1
% 1.48/1.01  --bmc1_max_bound_default                -1
% 1.48/1.01  --bmc1_symbol_reachability              true
% 1.48/1.01  --bmc1_property_lemmas                  false
% 1.48/1.01  --bmc1_k_induction                      false
% 1.48/1.01  --bmc1_non_equiv_states                 false
% 1.48/1.01  --bmc1_deadlock                         false
% 1.48/1.01  --bmc1_ucm                              false
% 1.48/1.01  --bmc1_add_unsat_core                   none
% 1.48/1.01  --bmc1_unsat_core_children              false
% 1.48/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.01  --bmc1_out_stat                         full
% 1.48/1.01  --bmc1_ground_init                      false
% 1.48/1.01  --bmc1_pre_inst_next_state              false
% 1.48/1.01  --bmc1_pre_inst_state                   false
% 1.48/1.01  --bmc1_pre_inst_reach_state             false
% 1.48/1.01  --bmc1_out_unsat_core                   false
% 1.48/1.01  --bmc1_aig_witness_out                  false
% 1.48/1.01  --bmc1_verbose                          false
% 1.48/1.01  --bmc1_dump_clauses_tptp                false
% 1.48/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.01  --bmc1_dump_file                        -
% 1.48/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.01  --bmc1_ucm_extend_mode                  1
% 1.48/1.01  --bmc1_ucm_init_mode                    2
% 1.48/1.01  --bmc1_ucm_cone_mode                    none
% 1.48/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.01  --bmc1_ucm_relax_model                  4
% 1.48/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.01  --bmc1_ucm_layered_model                none
% 1.48/1.01  --bmc1_ucm_max_lemma_size               10
% 1.48/1.01  
% 1.48/1.01  ------ AIG Options
% 1.48/1.01  
% 1.48/1.01  --aig_mode                              false
% 1.48/1.01  
% 1.48/1.01  ------ Instantiation Options
% 1.48/1.01  
% 1.48/1.01  --instantiation_flag                    true
% 1.48/1.01  --inst_sos_flag                         false
% 1.48/1.01  --inst_sos_phase                        true
% 1.48/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.01  --inst_lit_sel_side                     num_symb
% 1.48/1.01  --inst_solver_per_active                1400
% 1.48/1.01  --inst_solver_calls_frac                1.
% 1.48/1.01  --inst_passive_queue_type               priority_queues
% 1.48/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.01  --inst_passive_queues_freq              [25;2]
% 1.48/1.01  --inst_dismatching                      true
% 1.48/1.01  --inst_eager_unprocessed_to_passive     true
% 1.48/1.01  --inst_prop_sim_given                   true
% 1.48/1.01  --inst_prop_sim_new                     false
% 1.48/1.01  --inst_subs_new                         false
% 1.48/1.01  --inst_eq_res_simp                      false
% 1.48/1.01  --inst_subs_given                       false
% 1.48/1.01  --inst_orphan_elimination               true
% 1.48/1.01  --inst_learning_loop_flag               true
% 1.48/1.01  --inst_learning_start                   3000
% 1.48/1.01  --inst_learning_factor                  2
% 1.48/1.01  --inst_start_prop_sim_after_learn       3
% 1.48/1.01  --inst_sel_renew                        solver
% 1.48/1.01  --inst_lit_activity_flag                true
% 1.48/1.01  --inst_restr_to_given                   false
% 1.48/1.01  --inst_activity_threshold               500
% 1.48/1.01  --inst_out_proof                        true
% 1.48/1.01  
% 1.48/1.01  ------ Resolution Options
% 1.48/1.01  
% 1.48/1.01  --resolution_flag                       true
% 1.48/1.01  --res_lit_sel                           adaptive
% 1.48/1.01  --res_lit_sel_side                      none
% 1.48/1.01  --res_ordering                          kbo
% 1.48/1.01  --res_to_prop_solver                    active
% 1.48/1.01  --res_prop_simpl_new                    false
% 1.48/1.01  --res_prop_simpl_given                  true
% 1.48/1.01  --res_passive_queue_type                priority_queues
% 1.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.01  --res_passive_queues_freq               [15;5]
% 1.48/1.01  --res_forward_subs                      full
% 1.48/1.01  --res_backward_subs                     full
% 1.48/1.01  --res_forward_subs_resolution           true
% 1.48/1.01  --res_backward_subs_resolution          true
% 1.48/1.01  --res_orphan_elimination                true
% 1.48/1.01  --res_time_limit                        2.
% 1.48/1.01  --res_out_proof                         true
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Options
% 1.48/1.01  
% 1.48/1.01  --superposition_flag                    true
% 1.48/1.01  --sup_passive_queue_type                priority_queues
% 1.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.01  --demod_completeness_check              fast
% 1.48/1.01  --demod_use_ground                      true
% 1.48/1.01  --sup_to_prop_solver                    passive
% 1.48/1.01  --sup_prop_simpl_new                    true
% 1.48/1.01  --sup_prop_simpl_given                  true
% 1.48/1.01  --sup_fun_splitting                     false
% 1.48/1.01  --sup_smt_interval                      50000
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Simplification Setup
% 1.48/1.01  
% 1.48/1.01  --sup_indices_passive                   []
% 1.48/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_full_bw                           [BwDemod]
% 1.48/1.01  --sup_immed_triv                        [TrivRules]
% 1.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_immed_bw_main                     []
% 1.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  
% 1.48/1.01  ------ Combination Options
% 1.48/1.01  
% 1.48/1.01  --comb_res_mult                         3
% 1.48/1.01  --comb_sup_mult                         2
% 1.48/1.01  --comb_inst_mult                        10
% 1.48/1.01  
% 1.48/1.01  ------ Debug Options
% 1.48/1.01  
% 1.48/1.01  --dbg_backtrace                         false
% 1.48/1.01  --dbg_dump_prop_clauses                 false
% 1.48/1.01  --dbg_dump_prop_clauses_file            -
% 1.48/1.01  --dbg_out_stat                          false
% 1.48/1.01  ------ Parsing...
% 1.48/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.48/1.01  ------ Proving...
% 1.48/1.01  ------ Problem Properties 
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  clauses                                 21
% 1.48/1.01  conjectures                             1
% 1.48/1.01  EPR                                     3
% 1.48/1.01  Horn                                    15
% 1.48/1.01  unary                                   3
% 1.48/1.01  binary                                  9
% 1.48/1.01  lits                                    52
% 1.48/1.01  lits eq                                 27
% 1.48/1.01  fd_pure                                 0
% 1.48/1.01  fd_pseudo                               0
% 1.48/1.01  fd_cond                                 0
% 1.48/1.01  fd_pseudo_cond                          0
% 1.48/1.01  AC symbols                              0
% 1.48/1.01  
% 1.48/1.01  ------ Schedule dynamic 5 is on 
% 1.48/1.01  
% 1.48/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  ------ 
% 1.48/1.01  Current options:
% 1.48/1.01  ------ 
% 1.48/1.01  
% 1.48/1.01  ------ Input Options
% 1.48/1.01  
% 1.48/1.01  --out_options                           all
% 1.48/1.01  --tptp_safe_out                         true
% 1.48/1.01  --problem_path                          ""
% 1.48/1.01  --include_path                          ""
% 1.48/1.01  --clausifier                            res/vclausify_rel
% 1.48/1.01  --clausifier_options                    --mode clausify
% 1.48/1.01  --stdin                                 false
% 1.48/1.01  --stats_out                             all
% 1.48/1.01  
% 1.48/1.01  ------ General Options
% 1.48/1.01  
% 1.48/1.01  --fof                                   false
% 1.48/1.01  --time_out_real                         305.
% 1.48/1.01  --time_out_virtual                      -1.
% 1.48/1.01  --symbol_type_check                     false
% 1.48/1.01  --clausify_out                          false
% 1.48/1.01  --sig_cnt_out                           false
% 1.48/1.01  --trig_cnt_out                          false
% 1.48/1.01  --trig_cnt_out_tolerance                1.
% 1.48/1.01  --trig_cnt_out_sk_spl                   false
% 1.48/1.01  --abstr_cl_out                          false
% 1.48/1.01  
% 1.48/1.01  ------ Global Options
% 1.48/1.01  
% 1.48/1.01  --schedule                              default
% 1.48/1.01  --add_important_lit                     false
% 1.48/1.01  --prop_solver_per_cl                    1000
% 1.48/1.01  --min_unsat_core                        false
% 1.48/1.01  --soft_assumptions                      false
% 1.48/1.01  --soft_lemma_size                       3
% 1.48/1.01  --prop_impl_unit_size                   0
% 1.48/1.01  --prop_impl_unit                        []
% 1.48/1.01  --share_sel_clauses                     true
% 1.48/1.01  --reset_solvers                         false
% 1.48/1.01  --bc_imp_inh                            [conj_cone]
% 1.48/1.01  --conj_cone_tolerance                   3.
% 1.48/1.01  --extra_neg_conj                        none
% 1.48/1.01  --large_theory_mode                     true
% 1.48/1.01  --prolific_symb_bound                   200
% 1.48/1.01  --lt_threshold                          2000
% 1.48/1.01  --clause_weak_htbl                      true
% 1.48/1.01  --gc_record_bc_elim                     false
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing Options
% 1.48/1.01  
% 1.48/1.01  --preprocessing_flag                    true
% 1.48/1.01  --time_out_prep_mult                    0.1
% 1.48/1.01  --splitting_mode                        input
% 1.48/1.01  --splitting_grd                         true
% 1.48/1.01  --splitting_cvd                         false
% 1.48/1.01  --splitting_cvd_svl                     false
% 1.48/1.01  --splitting_nvd                         32
% 1.48/1.01  --sub_typing                            true
% 1.48/1.01  --prep_gs_sim                           true
% 1.48/1.01  --prep_unflatten                        true
% 1.48/1.01  --prep_res_sim                          true
% 1.48/1.01  --prep_upred                            true
% 1.48/1.01  --prep_sem_filter                       exhaustive
% 1.48/1.01  --prep_sem_filter_out                   false
% 1.48/1.01  --pred_elim                             true
% 1.48/1.01  --res_sim_input                         true
% 1.48/1.01  --eq_ax_congr_red                       true
% 1.48/1.01  --pure_diseq_elim                       true
% 1.48/1.01  --brand_transform                       false
% 1.48/1.01  --non_eq_to_eq                          false
% 1.48/1.01  --prep_def_merge                        true
% 1.48/1.01  --prep_def_merge_prop_impl              false
% 1.48/1.01  --prep_def_merge_mbd                    true
% 1.48/1.01  --prep_def_merge_tr_red                 false
% 1.48/1.01  --prep_def_merge_tr_cl                  false
% 1.48/1.01  --smt_preprocessing                     true
% 1.48/1.01  --smt_ac_axioms                         fast
% 1.48/1.01  --preprocessed_out                      false
% 1.48/1.01  --preprocessed_stats                    false
% 1.48/1.01  
% 1.48/1.01  ------ Abstraction refinement Options
% 1.48/1.01  
% 1.48/1.01  --abstr_ref                             []
% 1.48/1.01  --abstr_ref_prep                        false
% 1.48/1.01  --abstr_ref_until_sat                   false
% 1.48/1.01  --abstr_ref_sig_restrict                funpre
% 1.48/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.01  --abstr_ref_under                       []
% 1.48/1.01  
% 1.48/1.01  ------ SAT Options
% 1.48/1.01  
% 1.48/1.01  --sat_mode                              false
% 1.48/1.01  --sat_fm_restart_options                ""
% 1.48/1.01  --sat_gr_def                            false
% 1.48/1.01  --sat_epr_types                         true
% 1.48/1.01  --sat_non_cyclic_types                  false
% 1.48/1.01  --sat_finite_models                     false
% 1.48/1.01  --sat_fm_lemmas                         false
% 1.48/1.01  --sat_fm_prep                           false
% 1.48/1.01  --sat_fm_uc_incr                        true
% 1.48/1.01  --sat_out_model                         small
% 1.48/1.01  --sat_out_clauses                       false
% 1.48/1.01  
% 1.48/1.01  ------ QBF Options
% 1.48/1.01  
% 1.48/1.01  --qbf_mode                              false
% 1.48/1.01  --qbf_elim_univ                         false
% 1.48/1.01  --qbf_dom_inst                          none
% 1.48/1.01  --qbf_dom_pre_inst                      false
% 1.48/1.01  --qbf_sk_in                             false
% 1.48/1.01  --qbf_pred_elim                         true
% 1.48/1.01  --qbf_split                             512
% 1.48/1.01  
% 1.48/1.01  ------ BMC1 Options
% 1.48/1.01  
% 1.48/1.01  --bmc1_incremental                      false
% 1.48/1.01  --bmc1_axioms                           reachable_all
% 1.48/1.01  --bmc1_min_bound                        0
% 1.48/1.01  --bmc1_max_bound                        -1
% 1.48/1.01  --bmc1_max_bound_default                -1
% 1.48/1.01  --bmc1_symbol_reachability              true
% 1.48/1.01  --bmc1_property_lemmas                  false
% 1.48/1.01  --bmc1_k_induction                      false
% 1.48/1.01  --bmc1_non_equiv_states                 false
% 1.48/1.01  --bmc1_deadlock                         false
% 1.48/1.01  --bmc1_ucm                              false
% 1.48/1.01  --bmc1_add_unsat_core                   none
% 1.48/1.01  --bmc1_unsat_core_children              false
% 1.48/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.01  --bmc1_out_stat                         full
% 1.48/1.01  --bmc1_ground_init                      false
% 1.48/1.01  --bmc1_pre_inst_next_state              false
% 1.48/1.01  --bmc1_pre_inst_state                   false
% 1.48/1.01  --bmc1_pre_inst_reach_state             false
% 1.48/1.01  --bmc1_out_unsat_core                   false
% 1.48/1.01  --bmc1_aig_witness_out                  false
% 1.48/1.01  --bmc1_verbose                          false
% 1.48/1.01  --bmc1_dump_clauses_tptp                false
% 1.48/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.01  --bmc1_dump_file                        -
% 1.48/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.01  --bmc1_ucm_extend_mode                  1
% 1.48/1.01  --bmc1_ucm_init_mode                    2
% 1.48/1.01  --bmc1_ucm_cone_mode                    none
% 1.48/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.01  --bmc1_ucm_relax_model                  4
% 1.48/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.01  --bmc1_ucm_layered_model                none
% 1.48/1.01  --bmc1_ucm_max_lemma_size               10
% 1.48/1.01  
% 1.48/1.01  ------ AIG Options
% 1.48/1.01  
% 1.48/1.01  --aig_mode                              false
% 1.48/1.01  
% 1.48/1.01  ------ Instantiation Options
% 1.48/1.01  
% 1.48/1.01  --instantiation_flag                    true
% 1.48/1.01  --inst_sos_flag                         false
% 1.48/1.01  --inst_sos_phase                        true
% 1.48/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.01  --inst_lit_sel_side                     none
% 1.48/1.01  --inst_solver_per_active                1400
% 1.48/1.01  --inst_solver_calls_frac                1.
% 1.48/1.01  --inst_passive_queue_type               priority_queues
% 1.48/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.01  --inst_passive_queues_freq              [25;2]
% 1.48/1.01  --inst_dismatching                      true
% 1.48/1.01  --inst_eager_unprocessed_to_passive     true
% 1.48/1.01  --inst_prop_sim_given                   true
% 1.48/1.01  --inst_prop_sim_new                     false
% 1.48/1.01  --inst_subs_new                         false
% 1.48/1.01  --inst_eq_res_simp                      false
% 1.48/1.01  --inst_subs_given                       false
% 1.48/1.01  --inst_orphan_elimination               true
% 1.48/1.01  --inst_learning_loop_flag               true
% 1.48/1.01  --inst_learning_start                   3000
% 1.48/1.01  --inst_learning_factor                  2
% 1.48/1.01  --inst_start_prop_sim_after_learn       3
% 1.48/1.01  --inst_sel_renew                        solver
% 1.48/1.01  --inst_lit_activity_flag                true
% 1.48/1.01  --inst_restr_to_given                   false
% 1.48/1.01  --inst_activity_threshold               500
% 1.48/1.01  --inst_out_proof                        true
% 1.48/1.01  
% 1.48/1.01  ------ Resolution Options
% 1.48/1.01  
% 1.48/1.01  --resolution_flag                       false
% 1.48/1.01  --res_lit_sel                           adaptive
% 1.48/1.01  --res_lit_sel_side                      none
% 1.48/1.01  --res_ordering                          kbo
% 1.48/1.01  --res_to_prop_solver                    active
% 1.48/1.01  --res_prop_simpl_new                    false
% 1.48/1.01  --res_prop_simpl_given                  true
% 1.48/1.01  --res_passive_queue_type                priority_queues
% 1.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.01  --res_passive_queues_freq               [15;5]
% 1.48/1.01  --res_forward_subs                      full
% 1.48/1.01  --res_backward_subs                     full
% 1.48/1.01  --res_forward_subs_resolution           true
% 1.48/1.01  --res_backward_subs_resolution          true
% 1.48/1.01  --res_orphan_elimination                true
% 1.48/1.01  --res_time_limit                        2.
% 1.48/1.01  --res_out_proof                         true
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Options
% 1.48/1.01  
% 1.48/1.01  --superposition_flag                    true
% 1.48/1.01  --sup_passive_queue_type                priority_queues
% 1.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.01  --demod_completeness_check              fast
% 1.48/1.01  --demod_use_ground                      true
% 1.48/1.01  --sup_to_prop_solver                    passive
% 1.48/1.01  --sup_prop_simpl_new                    true
% 1.48/1.01  --sup_prop_simpl_given                  true
% 1.48/1.01  --sup_fun_splitting                     false
% 1.48/1.01  --sup_smt_interval                      50000
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Simplification Setup
% 1.48/1.01  
% 1.48/1.01  --sup_indices_passive                   []
% 1.48/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_full_bw                           [BwDemod]
% 1.48/1.01  --sup_immed_triv                        [TrivRules]
% 1.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_immed_bw_main                     []
% 1.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  
% 1.48/1.01  ------ Combination Options
% 1.48/1.01  
% 1.48/1.01  --comb_res_mult                         3
% 1.48/1.01  --comb_sup_mult                         2
% 1.48/1.01  --comb_inst_mult                        10
% 1.48/1.01  
% 1.48/1.01  ------ Debug Options
% 1.48/1.01  
% 1.48/1.01  --dbg_backtrace                         false
% 1.48/1.01  --dbg_dump_prop_clauses                 false
% 1.48/1.01  --dbg_dump_prop_clauses_file            -
% 1.48/1.01  --dbg_out_stat                          false
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  ------ Proving...
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  % SZS status Theorem for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01   Resolution empty clause
% 1.48/1.01  
% 1.48/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  fof(f5,axiom,(
% 1.48/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f16,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.48/1.01    inference(ennf_transformation,[],[f5])).
% 1.48/1.01  
% 1.48/1.01  fof(f17,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.48/1.01    inference(flattening,[],[f16])).
% 1.48/1.01  
% 1.48/1.01  fof(f44,plain,(
% 1.48/1.01    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f17])).
% 1.48/1.01  
% 1.48/1.01  fof(f9,conjecture,(
% 1.48/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f10,negated_conjecture,(
% 1.48/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.48/1.01    inference(negated_conjecture,[],[f9])).
% 1.48/1.01  
% 1.48/1.01  fof(f22,plain,(
% 1.48/1.01    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.48/1.01    inference(ennf_transformation,[],[f10])).
% 1.48/1.01  
% 1.48/1.01  fof(f23,plain,(
% 1.48/1.01    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.48/1.01    inference(flattening,[],[f22])).
% 1.48/1.01  
% 1.48/1.01  fof(f32,plain,(
% 1.48/1.01    ( ! [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_funct_2(X0,X0,sK2,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,sK2,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 1.48/1.01    introduced(choice_axiom,[])).
% 1.48/1.01  
% 1.48/1.01  fof(f31,plain,(
% 1.48/1.01    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK1,sK1,X1,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,X1,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X1,sK1,sK1) & v1_funct_1(X1)) & ~v1_xboole_0(sK1))),
% 1.48/1.01    introduced(choice_axiom,[])).
% 1.48/1.01  
% 1.48/1.01  fof(f33,plain,(
% 1.48/1.01    (~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) & ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)),
% 1.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f32,f31])).
% 1.48/1.01  
% 1.48/1.01  fof(f51,plain,(
% 1.48/1.01    v1_funct_2(sK2,sK1,sK1)),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f49,plain,(
% 1.48/1.01    ~v1_xboole_0(sK1)),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f50,plain,(
% 1.48/1.01    v1_funct_1(sK2)),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f52,plain,(
% 1.48/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f1,axiom,(
% 1.48/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f11,plain,(
% 1.48/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.48/1.01    inference(ennf_transformation,[],[f1])).
% 1.48/1.01  
% 1.48/1.01  fof(f24,plain,(
% 1.48/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.48/1.01    inference(nnf_transformation,[],[f11])).
% 1.48/1.01  
% 1.48/1.01  fof(f35,plain,(
% 1.48/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f24])).
% 1.48/1.01  
% 1.48/1.01  fof(f3,axiom,(
% 1.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f14,plain,(
% 1.48/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f3])).
% 1.48/1.01  
% 1.48/1.01  fof(f42,plain,(
% 1.48/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f14])).
% 1.48/1.01  
% 1.48/1.01  fof(f2,axiom,(
% 1.48/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f12,plain,(
% 1.48/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.48/1.01    inference(ennf_transformation,[],[f2])).
% 1.48/1.01  
% 1.48/1.01  fof(f13,plain,(
% 1.48/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(flattening,[],[f12])).
% 1.48/1.01  
% 1.48/1.01  fof(f25,plain,(
% 1.48/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(nnf_transformation,[],[f13])).
% 1.48/1.01  
% 1.48/1.01  fof(f26,plain,(
% 1.48/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(flattening,[],[f25])).
% 1.48/1.01  
% 1.48/1.01  fof(f27,plain,(
% 1.48/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(rectify,[],[f26])).
% 1.48/1.01  
% 1.48/1.01  fof(f28,plain,(
% 1.48/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.48/1.01    introduced(choice_axiom,[])).
% 1.48/1.01  
% 1.48/1.01  fof(f29,plain,(
% 1.48/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.48/1.01  
% 1.48/1.01  fof(f40,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f29])).
% 1.48/1.01  
% 1.48/1.01  fof(f6,axiom,(
% 1.48/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f45,plain,(
% 1.48/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f6])).
% 1.48/1.01  
% 1.48/1.01  fof(f56,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(definition_unfolding,[],[f40,f45])).
% 1.48/1.01  
% 1.48/1.01  fof(f60,plain,(
% 1.48/1.01    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(equality_resolution,[],[f56])).
% 1.48/1.01  
% 1.48/1.01  fof(f4,axiom,(
% 1.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f15,plain,(
% 1.48/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f4])).
% 1.48/1.01  
% 1.48/1.01  fof(f43,plain,(
% 1.48/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f15])).
% 1.48/1.01  
% 1.48/1.01  fof(f8,axiom,(
% 1.48/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f20,plain,(
% 1.48/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.48/1.01    inference(ennf_transformation,[],[f8])).
% 1.48/1.01  
% 1.48/1.01  fof(f21,plain,(
% 1.48/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.48/1.01    inference(flattening,[],[f20])).
% 1.48/1.01  
% 1.48/1.01  fof(f48,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f21])).
% 1.48/1.01  
% 1.48/1.01  fof(f53,plain,(
% 1.48/1.01    ( ! [X2] : (k3_funct_2(sK1,sK1,sK2,X2) = X2 | ~m1_subset_1(X2,sK1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f37,plain,(
% 1.48/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f24])).
% 1.48/1.01  
% 1.48/1.01  fof(f7,axiom,(
% 1.48/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f18,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/1.01    inference(ennf_transformation,[],[f7])).
% 1.48/1.01  
% 1.48/1.01  fof(f19,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/1.01    inference(flattening,[],[f18])).
% 1.48/1.01  
% 1.48/1.01  fof(f30,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/1.01    inference(nnf_transformation,[],[f19])).
% 1.48/1.01  
% 1.48/1.01  fof(f47,plain,(
% 1.48/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f30])).
% 1.48/1.01  
% 1.48/1.01  fof(f63,plain,(
% 1.48/1.01    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.48/1.01    inference(equality_resolution,[],[f47])).
% 1.48/1.01  
% 1.48/1.01  fof(f54,plain,(
% 1.48/1.01    ~r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1))),
% 1.48/1.01    inference(cnf_transformation,[],[f33])).
% 1.48/1.01  
% 1.48/1.01  fof(f41,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f29])).
% 1.48/1.01  
% 1.48/1.01  fof(f55,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(definition_unfolding,[],[f41,f45])).
% 1.48/1.01  
% 1.48/1.01  fof(f59,plain,(
% 1.48/1.01    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(equality_resolution,[],[f55])).
% 1.48/1.01  
% 1.48/1.01  cnf(c_10,plain,
% 1.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.48/1.01      | ~ m1_subset_1(X3,X1)
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | v1_xboole_0(X1)
% 1.48/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.48/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_17,negated_conjecture,
% 1.48/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_249,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,X1)
% 1.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.48/1.01      | ~ v1_funct_1(X2)
% 1.48/1.01      | v1_xboole_0(X1)
% 1.48/1.01      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.48/1.01      | sK2 != X2
% 1.48/1.01      | sK1 != X1
% 1.48/1.01      | sK1 != X3 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_250,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,sK1)
% 1.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | ~ v1_funct_1(sK2)
% 1.48/1.01      | v1_xboole_0(sK1)
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_249]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_19,negated_conjecture,
% 1.48/1.01      ( ~ v1_xboole_0(sK1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_18,negated_conjecture,
% 1.48/1.01      ( v1_funct_1(sK2) ),
% 1.48/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_16,negated_conjecture,
% 1.48/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.48/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_254,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,sK1)
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_250,c_19,c_18,c_16]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2,plain,
% 1.48/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_8,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.48/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_5,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.48/1.01      | ~ v1_relat_1(X0)
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.48/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_299,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 1.48/1.01      | ~ v1_relat_1(X0)
% 1.48/1.01      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.48/1.01      | sK2 != X0 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_300,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | ~ v1_relat_1(sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_299]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_435,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | sK2 != X0 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_300]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_436,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_435]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_438,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_436]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_440,plain,
% 1.48/1.01      ( r2_hidden(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_436,c_16,c_438]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_522,plain,
% 1.48/1.01      ( m1_subset_1(X0,X1)
% 1.48/1.01      | v1_xboole_0(X1)
% 1.48/1.01      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != X1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_440]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_523,plain,
% 1.48/1.01      ( m1_subset_1(sK0(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_522]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_735,plain,
% 1.48/1.01      ( v1_xboole_0(k1_relat_1(sK2))
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,X0) = k1_funct_1(sK2,X0)
% 1.48/1.01      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_254,c_523]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_736,plain,
% 1.48/1.01      ( v1_xboole_0(k1_relat_1(sK2))
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_735]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1722,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_737,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_9,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.48/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_662,plain,
% 1.48/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.48/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.48/1.01      | sK2 != X2 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_663,plain,
% 1.48/1.01      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.48/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_662]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1891,plain,
% 1.48/1.01      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 1.48/1.01      inference(equality_resolution,[status(thm)],[c_663]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_13,plain,
% 1.48/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.48/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_267,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | k1_relset_1(X1,X1,X0) = X1
% 1.48/1.01      | sK2 != X0
% 1.48/1.01      | sK1 != X1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_268,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | ~ v1_funct_1(sK2)
% 1.48/1.01      | k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_267]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_270,plain,
% 1.48/1.01      ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_268,c_18,c_16]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1892,plain,
% 1.48/1.01      ( k1_relat_1(sK2) = sK1 ),
% 1.48/1.01      inference(light_normalisation,[status(thm)],[c_1891,c_270]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2097,plain,
% 1.48/1.01      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_1722,c_737,c_1892]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2098,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2))
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(renaming,[status(thm)],[c_2097]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_15,negated_conjecture,
% 1.48/1.01      ( ~ m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK1,sK2,X0) = X0 ),
% 1.48/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_751,plain,
% 1.48/1.01      ( v1_xboole_0(k1_relat_1(sK2))
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,X0) = X0
% 1.48/1.01      | sK0(k1_relat_1(sK2),sK2) != X0
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_523]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_752,plain,
% 1.48/1.01      ( v1_xboole_0(k1_relat_1(sK2))
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_751]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1721,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_753,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k1_relat_1(sK2) != sK1
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2034,plain,
% 1.48/1.01      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_1721,c_753,c_1892]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2035,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(k1_relat_1(sK2),sK2)) = sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 1.48/1.01      inference(renaming,[status(thm)],[c_2034]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2038,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
% 1.48/1.01      | k6_partfun1(sK1) = sK2
% 1.48/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 1.48/1.01      inference(light_normalisation,[status(thm)],[c_2035,c_1892]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1735,plain,
% 1.48/1.01      ( v1_xboole_0(sK1) != iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_0,plain,
% 1.48/1.01      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_11,plain,
% 1.48/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 1.48/1.01      | ~ v1_funct_2(X2,X0,X1)
% 1.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.48/1.01      | ~ v1_funct_1(X2) ),
% 1.48/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_14,negated_conjecture,
% 1.48/1.01      ( ~ r2_funct_2(sK1,sK1,sK2,k6_partfun1(sK1)) ),
% 1.48/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_228,plain,
% 1.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | k6_partfun1(sK1) != X0
% 1.48/1.01      | sK2 != X0
% 1.48/1.01      | sK1 != X2
% 1.48/1.01      | sK1 != X1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_229,plain,
% 1.48/1.01      ( ~ v1_funct_2(k6_partfun1(sK1),sK1,sK1)
% 1.48/1.01      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.48/1.01      | sK2 != k6_partfun1(sK1) ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_228]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_275,plain,
% 1.48/1.01      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | ~ v1_funct_1(k6_partfun1(sK1))
% 1.48/1.01      | k6_partfun1(sK1) != sK2
% 1.48/1.01      | sK1 != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_229]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_356,plain,
% 1.48/1.01      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | k6_partfun1(sK1) != sK2
% 1.48/1.01      | sK1 != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_275]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_645,plain,
% 1.48/1.01      ( ~ v1_xboole_0(X0)
% 1.48/1.01      | ~ v1_xboole_0(X1)
% 1.48/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != X1
% 1.48/1.01      | k6_partfun1(sK1) != X0
% 1.48/1.01      | k6_partfun1(sK1) != sK2
% 1.48/1.01      | sK1 != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_356]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_646,plain,
% 1.48/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | ~ v1_xboole_0(k6_partfun1(sK1))
% 1.48/1.01      | k6_partfun1(sK1) != sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_645]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_767,plain,
% 1.48/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.48/1.01      | k6_partfun1(sK1) != sK2
% 1.48/1.01      | sK1 != sK1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_356]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1013,plain,
% 1.48/1.01      ( k6_partfun1(sK1) != sK2 ),
% 1.48/1.01      inference(equality_resolution_simp,[status(thm)],[c_767]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1020,plain,
% 1.48/1.01      ( k6_partfun1(sK1) != sK2 ),
% 1.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_646,c_1013]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2042,plain,
% 1.48/1.01      ( k3_funct_2(sK1,sK1,sK2,sK0(sK1,sK2)) = sK0(sK1,sK2) ),
% 1.48/1.01      inference(forward_subsumption_resolution,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_2038,c_1735,c_1020]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2101,plain,
% 1.48/1.01      ( k1_funct_1(sK2,sK0(sK1,sK2)) = sK0(sK1,sK2)
% 1.48/1.01      | k6_partfun1(sK1) = sK2
% 1.48/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 1.48/1.01      inference(light_normalisation,[status(thm)],[c_2098,c_1892,c_2042]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_4,plain,
% 1.48/1.01      ( ~ v1_relat_1(X0)
% 1.48/1.01      | ~ v1_funct_1(X0)
% 1.48/1.01      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.48/1.01      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 1.48/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_312,plain,
% 1.48/1.01      ( ~ v1_relat_1(X0)
% 1.48/1.01      | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
% 1.48/1.01      | k6_partfun1(k1_relat_1(X0)) = X0
% 1.48/1.01      | sK2 != X0 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_313,plain,
% 1.48/1.01      ( ~ v1_relat_1(sK2)
% 1.48/1.01      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_312]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_422,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 1.48/1.01      | sK2 != X0 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_313]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_423,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.48/1.01      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_422]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_425,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.48/1.01      | k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_423]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_427,plain,
% 1.48/1.01      ( k1_funct_1(sK2,sK0(k1_relat_1(sK2),sK2)) != sK0(k1_relat_1(sK2),sK2)
% 1.48/1.01      | k6_partfun1(k1_relat_1(sK2)) = sK2 ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_423,c_16,c_425]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1943,plain,
% 1.48/1.01      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) | k6_partfun1(sK1) = sK2 ),
% 1.48/1.01      inference(light_normalisation,[status(thm)],[c_427,c_1892]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1946,plain,
% 1.48/1.01      ( k1_funct_1(sK2,sK0(sK1,sK2)) != sK0(sK1,sK2) ),
% 1.48/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1943,c_1020]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2105,plain,
% 1.48/1.01      ( $false ),
% 1.48/1.01      inference(forward_subsumption_resolution,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_2101,c_1735,c_1020,c_1946]) ).
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  ------                               Statistics
% 1.48/1.01  
% 1.48/1.01  ------ General
% 1.48/1.01  
% 1.48/1.01  abstr_ref_over_cycles:                  0
% 1.48/1.01  abstr_ref_under_cycles:                 0
% 1.48/1.01  gc_basic_clause_elim:                   0
% 1.48/1.01  forced_gc_time:                         0
% 1.48/1.01  parsing_time:                           0.008
% 1.48/1.01  unif_index_cands_time:                  0.
% 1.48/1.01  unif_index_add_time:                    0.
% 1.48/1.01  orderings_time:                         0.
% 1.48/1.01  out_proof_time:                         0.01
% 1.48/1.01  total_time:                             0.09
% 1.48/1.01  num_of_symbols:                         52
% 1.48/1.01  num_of_terms:                           1026
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing
% 1.48/1.01  
% 1.48/1.01  num_of_splits:                          4
% 1.48/1.01  num_of_split_atoms:                     4
% 1.48/1.01  num_of_reused_defs:                     0
% 1.48/1.01  num_eq_ax_congr_red:                    5
% 1.48/1.01  num_of_sem_filtered_clauses:            1
% 1.48/1.01  num_of_subtypes:                        0
% 1.48/1.01  monotx_restored_types:                  0
% 1.48/1.01  sat_num_of_epr_types:                   0
% 1.48/1.01  sat_num_of_non_cyclic_types:            0
% 1.48/1.01  sat_guarded_non_collapsed_types:        0
% 1.48/1.01  num_pure_diseq_elim:                    0
% 1.48/1.01  simp_replaced_by:                       0
% 1.48/1.01  res_preprocessed:                       121
% 1.48/1.01  prep_upred:                             0
% 1.48/1.01  prep_unflattend:                        58
% 1.48/1.01  smt_new_axioms:                         0
% 1.48/1.01  pred_elim_cands:                        2
% 1.48/1.01  pred_elim:                              5
% 1.48/1.01  pred_elim_cl:                           1
% 1.48/1.01  pred_elim_cycles:                       11
% 1.48/1.01  merged_defs:                            0
% 1.48/1.01  merged_defs_ncl:                        0
% 1.48/1.01  bin_hyper_res:                          0
% 1.48/1.01  prep_cycles:                            5
% 1.48/1.01  pred_elim_time:                         0.019
% 1.48/1.01  splitting_time:                         0.
% 1.48/1.01  sem_filter_time:                        0.
% 1.48/1.01  monotx_time:                            0.
% 1.48/1.01  subtype_inf_time:                       0.
% 1.48/1.01  
% 1.48/1.01  ------ Problem properties
% 1.48/1.01  
% 1.48/1.01  clauses:                                21
% 1.48/1.01  conjectures:                            1
% 1.48/1.01  epr:                                    3
% 1.48/1.01  horn:                                   15
% 1.48/1.01  ground:                                 13
% 1.48/1.01  unary:                                  3
% 1.48/1.01  binary:                                 9
% 1.48/1.01  lits:                                   52
% 1.48/1.01  lits_eq:                                27
% 1.48/1.01  fd_pure:                                0
% 1.48/1.01  fd_pseudo:                              0
% 1.48/1.01  fd_cond:                                0
% 1.48/1.01  fd_pseudo_cond:                         0
% 1.48/1.01  ac_symbols:                             0
% 1.48/1.01  
% 1.48/1.01  ------ Propositional Solver
% 1.48/1.01  
% 1.48/1.01  prop_solver_calls:                      30
% 1.48/1.01  prop_fast_solver_calls:                 909
% 1.48/1.01  smt_solver_calls:                       0
% 1.48/1.01  smt_fast_solver_calls:                  0
% 1.48/1.01  prop_num_of_clauses:                    314
% 1.48/1.01  prop_preprocess_simplified:             2785
% 1.48/1.01  prop_fo_subsumed:                       13
% 1.48/1.01  prop_solver_time:                       0.
% 1.48/1.01  smt_solver_time:                        0.
% 1.48/1.01  smt_fast_solver_time:                   0.
% 1.48/1.01  prop_fast_solver_time:                  0.
% 1.48/1.01  prop_unsat_core_time:                   0.
% 1.48/1.01  
% 1.48/1.01  ------ QBF
% 1.48/1.01  
% 1.48/1.01  qbf_q_res:                              0
% 1.48/1.01  qbf_num_tautologies:                    0
% 1.48/1.01  qbf_prep_cycles:                        0
% 1.48/1.01  
% 1.48/1.01  ------ BMC1
% 1.48/1.01  
% 1.48/1.01  bmc1_current_bound:                     -1
% 1.48/1.01  bmc1_last_solved_bound:                 -1
% 1.48/1.01  bmc1_unsat_core_size:                   -1
% 1.48/1.01  bmc1_unsat_core_parents_size:           -1
% 1.48/1.01  bmc1_merge_next_fun:                    0
% 1.48/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.48/1.01  
% 1.48/1.01  ------ Instantiation
% 1.48/1.01  
% 1.48/1.01  inst_num_of_clauses:                    81
% 1.48/1.01  inst_num_in_passive:                    1
% 1.48/1.01  inst_num_in_active:                     67
% 1.48/1.01  inst_num_in_unprocessed:                13
% 1.48/1.01  inst_num_of_loops:                      80
% 1.48/1.01  inst_num_of_learning_restarts:          0
% 1.48/1.01  inst_num_moves_active_passive:          10
% 1.48/1.01  inst_lit_activity:                      0
% 1.48/1.01  inst_lit_activity_moves:                0
% 1.48/1.01  inst_num_tautologies:                   0
% 1.48/1.01  inst_num_prop_implied:                  0
% 1.48/1.01  inst_num_existing_simplified:           0
% 1.48/1.01  inst_num_eq_res_simplified:             0
% 1.48/1.01  inst_num_child_elim:                    0
% 1.48/1.01  inst_num_of_dismatching_blockings:      9
% 1.48/1.01  inst_num_of_non_proper_insts:           50
% 1.48/1.01  inst_num_of_duplicates:                 0
% 1.48/1.01  inst_inst_num_from_inst_to_res:         0
% 1.48/1.01  inst_dismatching_checking_time:         0.
% 1.48/1.01  
% 1.48/1.01  ------ Resolution
% 1.48/1.01  
% 1.48/1.01  res_num_of_clauses:                     0
% 1.48/1.01  res_num_in_passive:                     0
% 1.48/1.01  res_num_in_active:                      0
% 1.48/1.01  res_num_of_loops:                       126
% 1.48/1.01  res_forward_subset_subsumed:            27
% 1.48/1.01  res_backward_subset_subsumed:           0
% 1.48/1.01  res_forward_subsumed:                   0
% 1.48/1.01  res_backward_subsumed:                  2
% 1.48/1.01  res_forward_subsumption_resolution:     0
% 1.48/1.01  res_backward_subsumption_resolution:    0
% 1.48/1.01  res_clause_to_clause_subsumption:       39
% 1.48/1.01  res_orphan_elimination:                 0
% 1.48/1.01  res_tautology_del:                      17
% 1.48/1.01  res_num_eq_res_simplified:              2
% 1.48/1.01  res_num_sel_changes:                    0
% 1.48/1.01  res_moves_from_active_to_pass:          0
% 1.48/1.01  
% 1.48/1.01  ------ Superposition
% 1.48/1.01  
% 1.48/1.01  sup_time_total:                         0.
% 1.48/1.01  sup_time_generating:                    0.
% 1.48/1.01  sup_time_sim_full:                      0.
% 1.48/1.01  sup_time_sim_immed:                     0.
% 1.48/1.01  
% 1.48/1.01  sup_num_of_clauses:                     21
% 1.48/1.01  sup_num_in_active:                      14
% 1.48/1.01  sup_num_in_passive:                     7
% 1.48/1.01  sup_num_of_loops:                       15
% 1.48/1.01  sup_fw_superposition:                   0
% 1.48/1.01  sup_bw_superposition:                   0
% 1.48/1.01  sup_immediate_simplified:               1
% 1.48/1.01  sup_given_eliminated:                   0
% 1.48/1.01  comparisons_done:                       0
% 1.48/1.01  comparisons_avoided:                    0
% 1.48/1.01  
% 1.48/1.01  ------ Simplifications
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  sim_fw_subset_subsumed:                 0
% 1.48/1.01  sim_bw_subset_subsumed:                 0
% 1.48/1.01  sim_fw_subsumed:                        0
% 1.48/1.01  sim_bw_subsumed:                        0
% 1.48/1.01  sim_fw_subsumption_res:                 6
% 1.48/1.01  sim_bw_subsumption_res:                 0
% 1.48/1.01  sim_tautology_del:                      0
% 1.48/1.01  sim_eq_tautology_del:                   0
% 1.48/1.01  sim_eq_res_simp:                        0
% 1.48/1.01  sim_fw_demodulated:                     0
% 1.48/1.01  sim_bw_demodulated:                     1
% 1.48/1.01  sim_light_normalised:                   4
% 1.48/1.01  sim_joinable_taut:                      0
% 1.48/1.01  sim_joinable_simp:                      0
% 1.48/1.01  sim_ac_normalised:                      0
% 1.48/1.01  sim_smt_subsumption:                    0
% 1.48/1.01  
%------------------------------------------------------------------------------
