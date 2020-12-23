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
% DateTime   : Thu Dec  3 12:07:44 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  170 (1519 expanded)
%              Number of clauses        :  101 ( 463 expanded)
%              Number of leaves         :   20 ( 375 expanded)
%              Depth                    :   29
%              Number of atoms          :  565 (9616 expanded)
%              Number of equality atoms :  276 (2301 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(nnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f33,f51,f50])).

fof(f86,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1258,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_516,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_31])).

cnf(c_1243,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1245,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1609,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1243,c_1245])).

cnf(c_1781,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_516,c_1609])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_525,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_527,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_34])).

cnf(c_1241,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1610,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1241,c_1245])).

cnf(c_1938,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_527,c_1610])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1248,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3547,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1248])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1484,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_4224,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3547,c_40,c_42,c_1484])).

cnf(c_4225,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4224])).

cnf(c_4237,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_4225])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_375,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1487,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_782,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1661,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_783,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1512,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_2022,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_4379,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4237,c_37,c_39,c_31,c_375,c_1487,c_1661,c_2022])).

cnf(c_4385,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_4379])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1252,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4417,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_1252])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1244,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6097,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4417,c_1244])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1249,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6100,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6097,c_1249])).

cnf(c_6101,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6100])).

cnf(c_6151,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6100,c_36,c_34,c_33,c_31,c_375,c_1483,c_1486,c_1661,c_2022,c_6101])).

cnf(c_6155,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1781,c_6151])).

cnf(c_6156,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6155,c_1938])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1250,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3721,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1250])).

cnf(c_6166,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6156,c_3721])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6221,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6166,c_9])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6600,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6221,c_107])).

cnf(c_6608,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_6600])).

cnf(c_6615,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6608])).

cnf(c_3720,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1250])).

cnf(c_6167,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6156,c_3720])).

cnf(c_6216,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6167,c_9])).

cnf(c_6515,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6216,c_107])).

cnf(c_6523,plain,
    ( r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_6515])).

cnf(c_6530,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6523])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6115,plain,
    ( ~ r2_hidden(sK1(X0,sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6121,plain,
    ( r2_hidden(sK1(X0,sK5),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6115])).

cnf(c_6123,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6121])).

cnf(c_4154,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4160,plain,
    ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4154])).

cnf(c_4162,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4160])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1949,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1950,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_1952,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_1871,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK1(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1877,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1871])).

cnf(c_1879,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_1860,plain,
    ( r1_tarski(X0,sK6)
    | r2_hidden(sK1(X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1866,plain,
    ( r1_tarski(X0,sK6) = iProver_top
    | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_1868,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_1750,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1751,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1750])).

cnf(c_1753,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_1513,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6615,c_6530,c_6123,c_4162,c_1952,c_1879,c_1868,c_1753,c_1513,c_375,c_107,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.00/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.01  
% 3.00/1.01  ------  iProver source info
% 3.00/1.01  
% 3.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.01  git: non_committed_changes: false
% 3.00/1.01  git: last_make_outside_of_git: false
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  ------ Parsing...
% 3.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.01  ------ Proving...
% 3.00/1.01  ------ Problem Properties 
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  clauses                                 32
% 3.00/1.01  conjectures                             5
% 3.00/1.01  EPR                                     9
% 3.00/1.01  Horn                                    24
% 3.00/1.01  unary                                   10
% 3.00/1.01  binary                                  11
% 3.00/1.01  lits                                    75
% 3.00/1.01  lits eq                                 28
% 3.00/1.01  fd_pure                                 0
% 3.00/1.01  fd_pseudo                               0
% 3.00/1.01  fd_cond                                 1
% 3.00/1.01  fd_pseudo_cond                          3
% 3.00/1.01  AC symbols                              0
% 3.00/1.01  
% 3.00/1.01  ------ Schedule dynamic 5 is on 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  Current options:
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     none
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       false
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ Proving...
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS status Theorem for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  fof(f2,axiom,(
% 3.00/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f18,plain,(
% 3.00/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f2])).
% 3.00/1.01  
% 3.00/1.01  fof(f38,plain,(
% 3.00/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/1.01    inference(nnf_transformation,[],[f18])).
% 3.00/1.01  
% 3.00/1.01  fof(f39,plain,(
% 3.00/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/1.01    inference(rectify,[],[f38])).
% 3.00/1.01  
% 3.00/1.01  fof(f40,plain,(
% 3.00/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f41,plain,(
% 3.00/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.00/1.01  
% 3.00/1.01  fof(f56,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f41])).
% 3.00/1.01  
% 3.00/1.01  fof(f15,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f30,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f31,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(flattening,[],[f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f49,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f31])).
% 3.00/1.01  
% 3.00/1.01  fof(f76,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f49])).
% 3.00/1.01  
% 3.00/1.01  fof(f16,conjecture,(
% 3.00/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f17,negated_conjecture,(
% 3.00/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.00/1.01    inference(negated_conjecture,[],[f16])).
% 3.00/1.01  
% 3.00/1.01  fof(f32,plain,(
% 3.00/1.01    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.00/1.01    inference(ennf_transformation,[],[f17])).
% 3.00/1.01  
% 3.00/1.01  fof(f33,plain,(
% 3.00/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.00/1.01    inference(flattening,[],[f32])).
% 3.00/1.01  
% 3.00/1.01  fof(f51,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f50,plain,(
% 3.00/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f52,plain,(
% 3.00/1.01    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f33,f51,f50])).
% 3.00/1.01  
% 3.00/1.01  fof(f86,plain,(
% 3.00/1.01    v1_funct_2(sK6,sK3,sK4)),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f87,plain,(
% 3.00/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f13,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f27,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f13])).
% 3.00/1.01  
% 3.00/1.01  fof(f73,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f27])).
% 3.00/1.01  
% 3.00/1.01  fof(f83,plain,(
% 3.00/1.01    v1_funct_2(sK5,sK3,sK4)),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f84,plain,(
% 3.00/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f10,axiom,(
% 3.00/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f23,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f10])).
% 3.00/1.01  
% 3.00/1.01  fof(f24,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.01    inference(flattening,[],[f23])).
% 3.00/1.01  
% 3.00/1.01  fof(f46,plain,(
% 3.00/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f47,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f69,plain,(
% 3.00/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f47])).
% 3.00/1.01  
% 3.00/1.01  fof(f85,plain,(
% 3.00/1.01    v1_funct_1(sK6)),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f11,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f25,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f11])).
% 3.00/1.01  
% 3.00/1.01  fof(f71,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f25])).
% 3.00/1.01  
% 3.00/1.01  fof(f82,plain,(
% 3.00/1.01    v1_funct_1(sK5)),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f14,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f28,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.00/1.01    inference(ennf_transformation,[],[f14])).
% 3.00/1.01  
% 3.00/1.01  fof(f29,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(flattening,[],[f28])).
% 3.00/1.01  
% 3.00/1.01  fof(f48,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f29])).
% 3.00/1.01  
% 3.00/1.01  fof(f75,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f48])).
% 3.00/1.01  
% 3.00/1.01  fof(f94,plain,(
% 3.00/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(equality_resolution,[],[f75])).
% 3.00/1.01  
% 3.00/1.01  fof(f89,plain,(
% 3.00/1.01    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f7,axiom,(
% 3.00/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f19,plain,(
% 3.00/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f7])).
% 3.00/1.01  
% 3.00/1.01  fof(f66,plain,(
% 3.00/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f19])).
% 3.00/1.01  
% 3.00/1.01  fof(f88,plain,(
% 3.00/1.01    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f70,plain,(
% 3.00/1.01    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f47])).
% 3.00/1.01  
% 3.00/1.01  fof(f9,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f22,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f9])).
% 3.00/1.01  
% 3.00/1.01  fof(f68,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f22])).
% 3.00/1.01  
% 3.00/1.01  fof(f5,axiom,(
% 3.00/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f44,plain,(
% 3.00/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.01    inference(nnf_transformation,[],[f5])).
% 3.00/1.01  
% 3.00/1.01  fof(f45,plain,(
% 3.00/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.01    inference(flattening,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f64,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.00/1.01    inference(cnf_transformation,[],[f45])).
% 3.00/1.01  
% 3.00/1.01  fof(f92,plain,(
% 3.00/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.00/1.01    inference(equality_resolution,[],[f64])).
% 3.00/1.01  
% 3.00/1.01  fof(f3,axiom,(
% 3.00/1.01    v1_xboole_0(k1_xboole_0)),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f58,plain,(
% 3.00/1.01    v1_xboole_0(k1_xboole_0)),
% 3.00/1.01    inference(cnf_transformation,[],[f3])).
% 3.00/1.01  
% 3.00/1.01  fof(f1,axiom,(
% 3.00/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f34,plain,(
% 3.00/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.01    inference(nnf_transformation,[],[f1])).
% 3.00/1.01  
% 3.00/1.01  fof(f35,plain,(
% 3.00/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.01    inference(rectify,[],[f34])).
% 3.00/1.01  
% 3.00/1.01  fof(f36,plain,(
% 3.00/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f37,plain,(
% 3.00/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f53,plain,(
% 3.00/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f37])).
% 3.00/1.01  
% 3.00/1.01  fof(f4,axiom,(
% 3.00/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f42,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(nnf_transformation,[],[f4])).
% 3.00/1.01  
% 3.00/1.01  fof(f43,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(flattening,[],[f42])).
% 3.00/1.01  
% 3.00/1.01  fof(f61,plain,(
% 3.00/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f43])).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3,plain,
% 3.00/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1258,plain,
% 3.00/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.00/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_28,plain,
% 3.00/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.01      | k1_xboole_0 = X2 ),
% 3.00/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_32,negated_conjecture,
% 3.00/1.01      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.00/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_513,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.01      | sK6 != X0
% 3.00/1.01      | sK4 != X2
% 3.00/1.01      | sK3 != X1
% 3.00/1.01      | k1_xboole_0 = X2 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_514,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.01      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.00/1.01      | k1_xboole_0 = sK4 ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_513]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_31,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_516,plain,
% 3.00/1.01      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_514,c_31]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1243,plain,
% 3.00/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_20,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1245,plain,
% 3.00/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1609,plain,
% 3.00/1.01      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1243,c_1245]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1781,plain,
% 3.00/1.01      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_516,c_1609]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_35,negated_conjecture,
% 3.00/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.00/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_524,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.01      | sK5 != X0
% 3.00/1.01      | sK4 != X2
% 3.00/1.01      | sK3 != X1
% 3.00/1.01      | k1_xboole_0 = X2 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_525,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.01      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.00/1.01      | k1_xboole_0 = sK4 ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_524]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_34,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_527,plain,
% 3.00/1.01      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_525,c_34]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1241,plain,
% 3.00/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1610,plain,
% 3.00/1.01      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1241,c_1245]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1938,plain,
% 3.00/1.01      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_527,c_1610]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_17,plain,
% 3.00/1.01      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.00/1.01      | ~ v1_relat_1(X1)
% 3.00/1.01      | ~ v1_relat_1(X0)
% 3.00/1.01      | ~ v1_funct_1(X1)
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | X1 = X0
% 3.00/1.01      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1248,plain,
% 3.00/1.01      ( X0 = X1
% 3.00/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.00/1.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.00/1.01      | v1_relat_1(X1) != iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top
% 3.00/1.01      | v1_funct_1(X0) != iProver_top
% 3.00/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3547,plain,
% 3.00/1.01      ( k1_relat_1(X0) != sK3
% 3.00/1.01      | sK6 = X0
% 3.00/1.01      | sK4 = k1_xboole_0
% 3.00/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top
% 3.00/1.01      | v1_relat_1(sK6) != iProver_top
% 3.00/1.01      | v1_funct_1(X0) != iProver_top
% 3.00/1.01      | v1_funct_1(sK6) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1781,c_1248]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_33,negated_conjecture,
% 3.00/1.01      ( v1_funct_1(sK6) ),
% 3.00/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_40,plain,
% 3.00/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_42,plain,
% 3.00/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_18,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | v1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1483,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.01      | v1_relat_1(sK6) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1484,plain,
% 3.00/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.00/1.01      | v1_relat_1(sK6) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4224,plain,
% 3.00/1.01      ( v1_funct_1(X0) != iProver_top
% 3.00/1.01      | k1_relat_1(X0) != sK3
% 3.00/1.01      | sK6 = X0
% 3.00/1.01      | sK4 = k1_xboole_0
% 3.00/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_3547,c_40,c_42,c_1484]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4225,plain,
% 3.00/1.01      ( k1_relat_1(X0) != sK3
% 3.00/1.01      | sK6 = X0
% 3.00/1.01      | sK4 = k1_xboole_0
% 3.00/1.01      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top
% 3.00/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_4224]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4237,plain,
% 3.00/1.01      ( sK6 = sK5
% 3.00/1.01      | sK4 = k1_xboole_0
% 3.00/1.01      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 3.00/1.01      | v1_relat_1(sK5) != iProver_top
% 3.00/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1938,c_4225]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_36,negated_conjecture,
% 3.00/1.01      ( v1_funct_1(sK5) ),
% 3.00/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_37,plain,
% 3.00/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_39,plain,
% 3.00/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_21,plain,
% 3.00/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_29,negated_conjecture,
% 3.00/1.01      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.00/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_374,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | sK6 != X0
% 3.00/1.01      | sK5 != X0
% 3.00/1.01      | sK4 != X2
% 3.00/1.01      | sK3 != X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_375,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.01      | sK5 != sK6 ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1486,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.01      | v1_relat_1(sK5) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1487,plain,
% 3.00/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.00/1.01      | v1_relat_1(sK5) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_782,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1661,plain,
% 3.00/1.01      ( sK5 = sK5 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_782]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_783,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1512,plain,
% 3.00/1.01      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_783]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2022,plain,
% 3.00/1.01      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4379,plain,
% 3.00/1.01      ( sK4 = k1_xboole_0
% 3.00/1.01      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_4237,c_37,c_39,c_31,c_375,c_1487,c_1661,c_2022]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4385,plain,
% 3.00/1.01      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1938,c_4379]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_13,plain,
% 3.00/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1252,plain,
% 3.00/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.00/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4417,plain,
% 3.00/1.01      ( sK4 = k1_xboole_0 | m1_subset_1(sK2(sK5,sK6),sK3) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_4385,c_1252]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_30,negated_conjecture,
% 3.00/1.01      ( ~ m1_subset_1(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1244,plain,
% 3.00/1.01      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 3.00/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6097,plain,
% 3.00/1.01      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 3.00/1.01      | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_4417,c_1244]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_16,plain,
% 3.00/1.01      ( ~ v1_relat_1(X0)
% 3.00/1.01      | ~ v1_relat_1(X1)
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | ~ v1_funct_1(X1)
% 3.00/1.01      | X0 = X1
% 3.00/1.01      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.00/1.01      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1249,plain,
% 3.00/1.01      ( X0 = X1
% 3.00/1.01      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.00/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.00/1.01      | v1_relat_1(X0) != iProver_top
% 3.00/1.01      | v1_relat_1(X1) != iProver_top
% 3.00/1.01      | v1_funct_1(X1) != iProver_top
% 3.00/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6100,plain,
% 3.00/1.01      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.00/1.01      | sK6 = sK5
% 3.00/1.01      | sK4 = k1_xboole_0
% 3.00/1.01      | v1_relat_1(sK6) != iProver_top
% 3.00/1.01      | v1_relat_1(sK5) != iProver_top
% 3.00/1.01      | v1_funct_1(sK6) != iProver_top
% 3.00/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_6097,c_1249]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6101,plain,
% 3.00/1.01      ( ~ v1_relat_1(sK6)
% 3.00/1.01      | ~ v1_relat_1(sK5)
% 3.00/1.01      | ~ v1_funct_1(sK6)
% 3.00/1.01      | ~ v1_funct_1(sK5)
% 3.00/1.01      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.00/1.01      | sK6 = sK5
% 3.00/1.01      | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6100]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6151,plain,
% 3.00/1.01      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6100,c_36,c_34,c_33,c_31,c_375,c_1483,c_1486,c_1661,
% 3.00/1.01                 c_2022,c_6101]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6155,plain,
% 3.00/1.01      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1781,c_6151]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6156,plain,
% 3.00/1.01      ( sK4 = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6155,c_1938]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_15,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.01      | ~ r2_hidden(X2,X0)
% 3.00/1.01      | ~ v1_xboole_0(X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1250,plain,
% 3.00/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.00/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3721,plain,
% 3.00/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 3.00/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1241,c_1250]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6166,plain,
% 3.00/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 3.00/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6156,c_3721]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_9,plain,
% 3.00/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6221,plain,
% 3.00/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 3.00/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6166,c_9]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5,plain,
% 3.00/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_107,plain,
% 3.00/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6600,plain,
% 3.00/1.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6221,c_107]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6608,plain,
% 3.00/1.01      ( r1_tarski(sK5,X0) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1258,c_6600]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6615,plain,
% 3.00/1.01      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_6608]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3720,plain,
% 3.00/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 3.00/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1243,c_1250]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6167,plain,
% 3.00/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 3.00/1.01      | v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6156,c_3720]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6216,plain,
% 3.00/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 3.00/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_6167,c_9]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6515,plain,
% 3.00/1.01      ( r2_hidden(X0,sK6) != iProver_top ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6216,c_107]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6523,plain,
% 3.00/1.01      ( r1_tarski(sK6,X0) = iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1258,c_6515]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6530,plain,
% 3.00/1.01      ( r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_6523]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1,plain,
% 3.00/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6115,plain,
% 3.00/1.01      ( ~ r2_hidden(sK1(X0,sK5),X0) | ~ v1_xboole_0(X0) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6121,plain,
% 3.00/1.01      ( r2_hidden(sK1(X0,sK5),X0) != iProver_top
% 3.00/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_6115]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6123,plain,
% 3.00/1.01      ( r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
% 3.00/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_6121]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4154,plain,
% 3.00/1.01      ( ~ r2_hidden(sK1(X0,sK6),X0) | ~ v1_xboole_0(X0) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4160,plain,
% 3.00/1.01      ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
% 3.00/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_4154]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4162,plain,
% 3.00/1.01      ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
% 3.00/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_4160]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6,plain,
% 3.00/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1949,plain,
% 3.00/1.01      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1950,plain,
% 3.00/1.01      ( sK5 = X0
% 3.00/1.01      | r1_tarski(X0,sK5) != iProver_top
% 3.00/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1952,plain,
% 3.00/1.01      ( sK5 = k1_xboole_0
% 3.00/1.01      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.00/1.01      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1950]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1871,plain,
% 3.00/1.01      ( r1_tarski(X0,sK5) | r2_hidden(sK1(X0,sK5),X0) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1877,plain,
% 3.00/1.01      ( r1_tarski(X0,sK5) = iProver_top
% 3.00/1.01      | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1871]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1879,plain,
% 3.00/1.01      ( r1_tarski(k1_xboole_0,sK5) = iProver_top
% 3.00/1.01      | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1877]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1860,plain,
% 3.00/1.01      ( r1_tarski(X0,sK6) | r2_hidden(sK1(X0,sK6),X0) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1866,plain,
% 3.00/1.01      ( r1_tarski(X0,sK6) = iProver_top
% 3.00/1.01      | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1868,plain,
% 3.00/1.01      ( r1_tarski(k1_xboole_0,sK6) = iProver_top
% 3.00/1.01      | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1866]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1750,plain,
% 3.00/1.01      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1751,plain,
% 3.00/1.01      ( sK6 = X0
% 3.00/1.01      | r1_tarski(X0,sK6) != iProver_top
% 3.00/1.01      | r1_tarski(sK6,X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1750]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1753,plain,
% 3.00/1.01      ( sK6 = k1_xboole_0
% 3.00/1.01      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 3.00/1.01      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1751]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1513,plain,
% 3.00/1.01      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(contradiction,plain,
% 3.00/1.01      ( $false ),
% 3.00/1.01      inference(minisat,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_6615,c_6530,c_6123,c_4162,c_1952,c_1879,c_1868,c_1753,
% 3.00/1.01                 c_1513,c_375,c_107,c_31]) ).
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  ------                               Statistics
% 3.00/1.01  
% 3.00/1.01  ------ General
% 3.00/1.01  
% 3.00/1.01  abstr_ref_over_cycles:                  0
% 3.00/1.01  abstr_ref_under_cycles:                 0
% 3.00/1.01  gc_basic_clause_elim:                   0
% 3.00/1.01  forced_gc_time:                         0
% 3.00/1.01  parsing_time:                           0.015
% 3.00/1.01  unif_index_cands_time:                  0.
% 3.00/1.01  unif_index_add_time:                    0.
% 3.00/1.01  orderings_time:                         0.
% 3.00/1.01  out_proof_time:                         0.015
% 3.00/1.01  total_time:                             0.363
% 3.00/1.01  num_of_symbols:                         52
% 3.00/1.01  num_of_terms:                           6624
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing
% 3.00/1.01  
% 3.00/1.01  num_of_splits:                          0
% 3.00/1.01  num_of_split_atoms:                     0
% 3.00/1.01  num_of_reused_defs:                     0
% 3.00/1.01  num_eq_ax_congr_red:                    29
% 3.00/1.01  num_of_sem_filtered_clauses:            1
% 3.00/1.01  num_of_subtypes:                        0
% 3.00/1.01  monotx_restored_types:                  0
% 3.00/1.01  sat_num_of_epr_types:                   0
% 3.00/1.01  sat_num_of_non_cyclic_types:            0
% 3.00/1.01  sat_guarded_non_collapsed_types:        0
% 3.00/1.01  num_pure_diseq_elim:                    0
% 3.00/1.01  simp_replaced_by:                       0
% 3.00/1.01  res_preprocessed:                       153
% 3.00/1.01  prep_upred:                             0
% 3.00/1.01  prep_unflattend:                        49
% 3.00/1.01  smt_new_axioms:                         0
% 3.00/1.01  pred_elim_cands:                        6
% 3.00/1.01  pred_elim:                              2
% 3.00/1.01  pred_elim_cl:                           4
% 3.00/1.01  pred_elim_cycles:                       5
% 3.00/1.01  merged_defs:                            0
% 3.00/1.01  merged_defs_ncl:                        0
% 3.00/1.01  bin_hyper_res:                          0
% 3.00/1.01  prep_cycles:                            4
% 3.00/1.01  pred_elim_time:                         0.005
% 3.00/1.01  splitting_time:                         0.
% 3.00/1.01  sem_filter_time:                        0.
% 3.00/1.01  monotx_time:                            0.
% 3.00/1.01  subtype_inf_time:                       0.
% 3.00/1.01  
% 3.00/1.01  ------ Problem properties
% 3.00/1.01  
% 3.00/1.01  clauses:                                32
% 3.00/1.01  conjectures:                            5
% 3.00/1.01  epr:                                    9
% 3.00/1.01  horn:                                   24
% 3.00/1.01  ground:                                 12
% 3.00/1.01  unary:                                  10
% 3.00/1.01  binary:                                 11
% 3.00/1.01  lits:                                   75
% 3.00/1.01  lits_eq:                                28
% 3.00/1.01  fd_pure:                                0
% 3.00/1.01  fd_pseudo:                              0
% 3.00/1.01  fd_cond:                                1
% 3.00/1.01  fd_pseudo_cond:                         3
% 3.00/1.01  ac_symbols:                             0
% 3.00/1.01  
% 3.00/1.01  ------ Propositional Solver
% 3.00/1.01  
% 3.00/1.01  prop_solver_calls:                      28
% 3.00/1.01  prop_fast_solver_calls:                 1045
% 3.00/1.01  smt_solver_calls:                       0
% 3.00/1.01  smt_fast_solver_calls:                  0
% 3.00/1.01  prop_num_of_clauses:                    2320
% 3.00/1.01  prop_preprocess_simplified:             7495
% 3.00/1.01  prop_fo_subsumed:                       31
% 3.00/1.01  prop_solver_time:                       0.
% 3.00/1.01  smt_solver_time:                        0.
% 3.00/1.01  smt_fast_solver_time:                   0.
% 3.00/1.01  prop_fast_solver_time:                  0.
% 3.00/1.01  prop_unsat_core_time:                   0.
% 3.00/1.01  
% 3.00/1.01  ------ QBF
% 3.00/1.01  
% 3.00/1.01  qbf_q_res:                              0
% 3.00/1.01  qbf_num_tautologies:                    0
% 3.00/1.01  qbf_prep_cycles:                        0
% 3.00/1.01  
% 3.00/1.01  ------ BMC1
% 3.00/1.01  
% 3.00/1.01  bmc1_current_bound:                     -1
% 3.00/1.01  bmc1_last_solved_bound:                 -1
% 3.00/1.01  bmc1_unsat_core_size:                   -1
% 3.00/1.01  bmc1_unsat_core_parents_size:           -1
% 3.00/1.01  bmc1_merge_next_fun:                    0
% 3.00/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation
% 3.00/1.01  
% 3.00/1.01  inst_num_of_clauses:                    855
% 3.00/1.01  inst_num_in_passive:                    357
% 3.00/1.01  inst_num_in_active:                     353
% 3.00/1.01  inst_num_in_unprocessed:                145
% 3.00/1.01  inst_num_of_loops:                      440
% 3.00/1.01  inst_num_of_learning_restarts:          0
% 3.00/1.01  inst_num_moves_active_passive:          85
% 3.00/1.01  inst_lit_activity:                      0
% 3.00/1.01  inst_lit_activity_moves:                0
% 3.00/1.01  inst_num_tautologies:                   0
% 3.00/1.01  inst_num_prop_implied:                  0
% 3.00/1.01  inst_num_existing_simplified:           0
% 3.00/1.01  inst_num_eq_res_simplified:             0
% 3.00/1.01  inst_num_child_elim:                    0
% 3.00/1.01  inst_num_of_dismatching_blockings:      232
% 3.00/1.01  inst_num_of_non_proper_insts:           796
% 3.00/1.01  inst_num_of_duplicates:                 0
% 3.00/1.01  inst_inst_num_from_inst_to_res:         0
% 3.00/1.01  inst_dismatching_checking_time:         0.
% 3.00/1.01  
% 3.00/1.01  ------ Resolution
% 3.00/1.01  
% 3.00/1.01  res_num_of_clauses:                     0
% 3.00/1.01  res_num_in_passive:                     0
% 3.00/1.01  res_num_in_active:                      0
% 3.00/1.01  res_num_of_loops:                       157
% 3.00/1.01  res_forward_subset_subsumed:            75
% 3.00/1.01  res_backward_subset_subsumed:           0
% 3.00/1.01  res_forward_subsumed:                   0
% 3.00/1.01  res_backward_subsumed:                  0
% 3.00/1.01  res_forward_subsumption_resolution:     0
% 3.00/1.01  res_backward_subsumption_resolution:    0
% 3.00/1.01  res_clause_to_clause_subsumption:       393
% 3.00/1.01  res_orphan_elimination:                 0
% 3.00/1.01  res_tautology_del:                      47
% 3.00/1.01  res_num_eq_res_simplified:              0
% 3.00/1.01  res_num_sel_changes:                    0
% 3.00/1.01  res_moves_from_active_to_pass:          0
% 3.00/1.01  
% 3.00/1.01  ------ Superposition
% 3.00/1.01  
% 3.00/1.01  sup_time_total:                         0.
% 3.00/1.01  sup_time_generating:                    0.
% 3.00/1.01  sup_time_sim_full:                      0.
% 3.00/1.01  sup_time_sim_immed:                     0.
% 3.00/1.01  
% 3.00/1.01  sup_num_of_clauses:                     121
% 3.00/1.01  sup_num_in_active:                      59
% 3.00/1.01  sup_num_in_passive:                     62
% 3.00/1.01  sup_num_of_loops:                       86
% 3.00/1.01  sup_fw_superposition:                   106
% 3.00/1.01  sup_bw_superposition:                   68
% 3.00/1.01  sup_immediate_simplified:               76
% 3.00/1.01  sup_given_eliminated:                   0
% 3.00/1.01  comparisons_done:                       0
% 3.00/1.01  comparisons_avoided:                    9
% 3.00/1.01  
% 3.00/1.01  ------ Simplifications
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  sim_fw_subset_subsumed:                 2
% 3.00/1.01  sim_bw_subset_subsumed:                 16
% 3.00/1.01  sim_fw_subsumed:                        16
% 3.00/1.01  sim_bw_subsumed:                        0
% 3.00/1.01  sim_fw_subsumption_res:                 4
% 3.00/1.01  sim_bw_subsumption_res:                 0
% 3.00/1.01  sim_tautology_del:                      1
% 3.00/1.01  sim_eq_tautology_del:                   14
% 3.00/1.01  sim_eq_res_simp:                        2
% 3.00/1.01  sim_fw_demodulated:                     32
% 3.00/1.01  sim_bw_demodulated:                     43
% 3.00/1.01  sim_light_normalised:                   2
% 3.00/1.01  sim_joinable_taut:                      0
% 3.00/1.01  sim_joinable_simp:                      0
% 3.00/1.01  sim_ac_normalised:                      0
% 3.00/1.01  sim_smt_subsumption:                    0
% 3.00/1.01  
%------------------------------------------------------------------------------
