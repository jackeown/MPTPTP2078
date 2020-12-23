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
% DateTime   : Thu Dec  3 12:01:12 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  135 (1488 expanded)
%              Number of clauses        :   84 ( 428 expanded)
%              Number of leaves         :   14 ( 373 expanded)
%              Depth                    :   25
%              Number of atoms          :  465 (9960 expanded)
%              Number of equality atoms :  243 (2263 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f45,f44])).

fof(f78,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_513,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_29])).

cnf(c_2036,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2038,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2419,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2036,c_2038])).

cnf(c_2583,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_513,c_2419])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_522,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_524,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_32])).

cnf(c_2034,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2420,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2034,c_2038])).

cnf(c_2659,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_524,c_2420])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2040,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3222,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_2040])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2283,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2284,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2283])).

cnf(c_3837,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3222,c_38,c_40,c_2284])).

cnf(c_3838,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3837])).

cnf(c_3850,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_3838])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_20,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_29])).

cnf(c_744,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | sK6 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_420])).

cnf(c_745,plain,
    ( sK6 != sK5 ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_2286,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2287,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2286])).

cnf(c_3863,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_35,c_37,c_745,c_2287])).

cnf(c_3869,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_3863])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2037,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4093,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3869,c_2037])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2041,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4254,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_2041])).

cnf(c_4270,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4254])).

cnf(c_5471,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4254,c_34,c_32,c_31,c_29,c_745,c_2283,c_2286,c_4270])).

cnf(c_5475,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2583,c_5471])).

cnf(c_5512,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5475,c_2659])).

cnf(c_5534,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5512,c_2036])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5540,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5534,c_11])).

cnf(c_5535,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5512,c_2034])).

cnf(c_5537,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5535,c_11])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3626,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3627,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3626])).

cnf(c_3629,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3627])).

cnf(c_3436,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3437,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3436])).

cnf(c_3439,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3421,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3424,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3421])).

cnf(c_1393,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2381,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_2786,plain,
    ( sK6 != X0
    | sK6 = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2381])).

cnf(c_2788,plain,
    ( sK6 = sK5
    | sK6 != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2665,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2671,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2665])).

cnf(c_2673,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2647,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2650,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_2587,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2593,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_2595,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5540,c_5537,c_3629,c_3439,c_3424,c_2788,c_2673,c_2650,c_2595,c_745])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:48:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.90/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/0.96  
% 2.90/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/0.96  
% 2.90/0.96  ------  iProver source info
% 2.90/0.96  
% 2.90/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.90/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/0.96  git: non_committed_changes: false
% 2.90/0.96  git: last_make_outside_of_git: false
% 2.90/0.96  
% 2.90/0.96  ------ 
% 2.90/0.96  
% 2.90/0.96  ------ Input Options
% 2.90/0.96  
% 2.90/0.96  --out_options                           all
% 2.90/0.96  --tptp_safe_out                         true
% 2.90/0.96  --problem_path                          ""
% 2.90/0.96  --include_path                          ""
% 2.90/0.96  --clausifier                            res/vclausify_rel
% 2.90/0.96  --clausifier_options                    --mode clausify
% 2.90/0.96  --stdin                                 false
% 2.90/0.96  --stats_out                             all
% 2.90/0.96  
% 2.90/0.96  ------ General Options
% 2.90/0.96  
% 2.90/0.96  --fof                                   false
% 2.90/0.96  --time_out_real                         305.
% 2.90/0.96  --time_out_virtual                      -1.
% 2.90/0.96  --symbol_type_check                     false
% 2.90/0.96  --clausify_out                          false
% 2.90/0.96  --sig_cnt_out                           false
% 2.90/0.96  --trig_cnt_out                          false
% 2.90/0.96  --trig_cnt_out_tolerance                1.
% 2.90/0.96  --trig_cnt_out_sk_spl                   false
% 2.90/0.96  --abstr_cl_out                          false
% 2.90/0.96  
% 2.90/0.96  ------ Global Options
% 2.90/0.96  
% 2.90/0.96  --schedule                              default
% 2.90/0.96  --add_important_lit                     false
% 2.90/0.96  --prop_solver_per_cl                    1000
% 2.90/0.96  --min_unsat_core                        false
% 2.90/0.96  --soft_assumptions                      false
% 2.90/0.96  --soft_lemma_size                       3
% 2.90/0.96  --prop_impl_unit_size                   0
% 2.90/0.96  --prop_impl_unit                        []
% 2.90/0.96  --share_sel_clauses                     true
% 2.90/0.96  --reset_solvers                         false
% 2.90/0.96  --bc_imp_inh                            [conj_cone]
% 2.90/0.96  --conj_cone_tolerance                   3.
% 2.90/0.96  --extra_neg_conj                        none
% 2.90/0.96  --large_theory_mode                     true
% 2.90/0.96  --prolific_symb_bound                   200
% 2.90/0.96  --lt_threshold                          2000
% 2.90/0.96  --clause_weak_htbl                      true
% 2.90/0.96  --gc_record_bc_elim                     false
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing Options
% 2.90/0.96  
% 2.90/0.96  --preprocessing_flag                    true
% 2.90/0.96  --time_out_prep_mult                    0.1
% 2.90/0.96  --splitting_mode                        input
% 2.90/0.96  --splitting_grd                         true
% 2.90/0.96  --splitting_cvd                         false
% 2.90/0.96  --splitting_cvd_svl                     false
% 2.90/0.96  --splitting_nvd                         32
% 2.90/0.96  --sub_typing                            true
% 2.90/0.96  --prep_gs_sim                           true
% 2.90/0.96  --prep_unflatten                        true
% 2.90/0.96  --prep_res_sim                          true
% 2.90/0.96  --prep_upred                            true
% 2.90/0.96  --prep_sem_filter                       exhaustive
% 2.90/0.96  --prep_sem_filter_out                   false
% 2.90/0.96  --pred_elim                             true
% 2.90/0.96  --res_sim_input                         true
% 2.90/0.96  --eq_ax_congr_red                       true
% 2.90/0.96  --pure_diseq_elim                       true
% 2.90/0.96  --brand_transform                       false
% 2.90/0.96  --non_eq_to_eq                          false
% 2.90/0.96  --prep_def_merge                        true
% 2.90/0.96  --prep_def_merge_prop_impl              false
% 2.90/0.96  --prep_def_merge_mbd                    true
% 2.90/0.96  --prep_def_merge_tr_red                 false
% 2.90/0.96  --prep_def_merge_tr_cl                  false
% 2.90/0.96  --smt_preprocessing                     true
% 2.90/0.96  --smt_ac_axioms                         fast
% 2.90/0.96  --preprocessed_out                      false
% 2.90/0.96  --preprocessed_stats                    false
% 2.90/0.96  
% 2.90/0.96  ------ Abstraction refinement Options
% 2.90/0.96  
% 2.90/0.96  --abstr_ref                             []
% 2.90/0.96  --abstr_ref_prep                        false
% 2.90/0.96  --abstr_ref_until_sat                   false
% 2.90/0.96  --abstr_ref_sig_restrict                funpre
% 2.90/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.96  --abstr_ref_under                       []
% 2.90/0.96  
% 2.90/0.96  ------ SAT Options
% 2.90/0.96  
% 2.90/0.96  --sat_mode                              false
% 2.90/0.96  --sat_fm_restart_options                ""
% 2.90/0.96  --sat_gr_def                            false
% 2.90/0.96  --sat_epr_types                         true
% 2.90/0.96  --sat_non_cyclic_types                  false
% 2.90/0.96  --sat_finite_models                     false
% 2.90/0.96  --sat_fm_lemmas                         false
% 2.90/0.96  --sat_fm_prep                           false
% 2.90/0.96  --sat_fm_uc_incr                        true
% 2.90/0.96  --sat_out_model                         small
% 2.90/0.96  --sat_out_clauses                       false
% 2.90/0.96  
% 2.90/0.96  ------ QBF Options
% 2.90/0.96  
% 2.90/0.96  --qbf_mode                              false
% 2.90/0.96  --qbf_elim_univ                         false
% 2.90/0.96  --qbf_dom_inst                          none
% 2.90/0.96  --qbf_dom_pre_inst                      false
% 2.90/0.96  --qbf_sk_in                             false
% 2.90/0.96  --qbf_pred_elim                         true
% 2.90/0.96  --qbf_split                             512
% 2.90/0.96  
% 2.90/0.96  ------ BMC1 Options
% 2.90/0.96  
% 2.90/0.96  --bmc1_incremental                      false
% 2.90/0.96  --bmc1_axioms                           reachable_all
% 2.90/0.96  --bmc1_min_bound                        0
% 2.90/0.96  --bmc1_max_bound                        -1
% 2.90/0.96  --bmc1_max_bound_default                -1
% 2.90/0.96  --bmc1_symbol_reachability              true
% 2.90/0.96  --bmc1_property_lemmas                  false
% 2.90/0.96  --bmc1_k_induction                      false
% 2.90/0.96  --bmc1_non_equiv_states                 false
% 2.90/0.96  --bmc1_deadlock                         false
% 2.90/0.96  --bmc1_ucm                              false
% 2.90/0.96  --bmc1_add_unsat_core                   none
% 2.90/0.96  --bmc1_unsat_core_children              false
% 2.90/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.96  --bmc1_out_stat                         full
% 2.90/0.96  --bmc1_ground_init                      false
% 2.90/0.96  --bmc1_pre_inst_next_state              false
% 2.90/0.96  --bmc1_pre_inst_state                   false
% 2.90/0.96  --bmc1_pre_inst_reach_state             false
% 2.90/0.96  --bmc1_out_unsat_core                   false
% 2.90/0.96  --bmc1_aig_witness_out                  false
% 2.90/0.96  --bmc1_verbose                          false
% 2.90/0.96  --bmc1_dump_clauses_tptp                false
% 2.90/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.96  --bmc1_dump_file                        -
% 2.90/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.96  --bmc1_ucm_extend_mode                  1
% 2.90/0.96  --bmc1_ucm_init_mode                    2
% 2.90/0.96  --bmc1_ucm_cone_mode                    none
% 2.90/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.96  --bmc1_ucm_relax_model                  4
% 2.90/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.96  --bmc1_ucm_layered_model                none
% 2.90/0.96  --bmc1_ucm_max_lemma_size               10
% 2.90/0.96  
% 2.90/0.96  ------ AIG Options
% 2.90/0.96  
% 2.90/0.96  --aig_mode                              false
% 2.90/0.96  
% 2.90/0.96  ------ Instantiation Options
% 2.90/0.96  
% 2.90/0.96  --instantiation_flag                    true
% 2.90/0.96  --inst_sos_flag                         false
% 2.90/0.96  --inst_sos_phase                        true
% 2.90/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.96  --inst_lit_sel_side                     num_symb
% 2.90/0.96  --inst_solver_per_active                1400
% 2.90/0.96  --inst_solver_calls_frac                1.
% 2.90/0.96  --inst_passive_queue_type               priority_queues
% 2.90/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.96  --inst_passive_queues_freq              [25;2]
% 2.90/0.96  --inst_dismatching                      true
% 2.90/0.96  --inst_eager_unprocessed_to_passive     true
% 2.90/0.96  --inst_prop_sim_given                   true
% 2.90/0.96  --inst_prop_sim_new                     false
% 2.90/0.96  --inst_subs_new                         false
% 2.90/0.96  --inst_eq_res_simp                      false
% 2.90/0.96  --inst_subs_given                       false
% 2.90/0.96  --inst_orphan_elimination               true
% 2.90/0.96  --inst_learning_loop_flag               true
% 2.90/0.96  --inst_learning_start                   3000
% 2.90/0.96  --inst_learning_factor                  2
% 2.90/0.96  --inst_start_prop_sim_after_learn       3
% 2.90/0.96  --inst_sel_renew                        solver
% 2.90/0.96  --inst_lit_activity_flag                true
% 2.90/0.96  --inst_restr_to_given                   false
% 2.90/0.96  --inst_activity_threshold               500
% 2.90/0.96  --inst_out_proof                        true
% 2.90/0.96  
% 2.90/0.96  ------ Resolution Options
% 2.90/0.96  
% 2.90/0.96  --resolution_flag                       true
% 2.90/0.96  --res_lit_sel                           adaptive
% 2.90/0.96  --res_lit_sel_side                      none
% 2.90/0.96  --res_ordering                          kbo
% 2.90/0.96  --res_to_prop_solver                    active
% 2.90/0.96  --res_prop_simpl_new                    false
% 2.90/0.96  --res_prop_simpl_given                  true
% 2.90/0.96  --res_passive_queue_type                priority_queues
% 2.90/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.96  --res_passive_queues_freq               [15;5]
% 2.90/0.96  --res_forward_subs                      full
% 2.90/0.96  --res_backward_subs                     full
% 2.90/0.96  --res_forward_subs_resolution           true
% 2.90/0.96  --res_backward_subs_resolution          true
% 2.90/0.96  --res_orphan_elimination                true
% 2.90/0.96  --res_time_limit                        2.
% 2.90/0.96  --res_out_proof                         true
% 2.90/0.96  
% 2.90/0.96  ------ Superposition Options
% 2.90/0.96  
% 2.90/0.96  --superposition_flag                    true
% 2.90/0.96  --sup_passive_queue_type                priority_queues
% 2.90/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.96  --demod_completeness_check              fast
% 2.90/0.96  --demod_use_ground                      true
% 2.90/0.96  --sup_to_prop_solver                    passive
% 2.90/0.96  --sup_prop_simpl_new                    true
% 2.90/0.96  --sup_prop_simpl_given                  true
% 2.90/0.96  --sup_fun_splitting                     false
% 2.90/0.96  --sup_smt_interval                      50000
% 2.90/0.96  
% 2.90/0.96  ------ Superposition Simplification Setup
% 2.90/0.96  
% 2.90/0.96  --sup_indices_passive                   []
% 2.90/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_full_bw                           [BwDemod]
% 2.90/0.96  --sup_immed_triv                        [TrivRules]
% 2.90/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_immed_bw_main                     []
% 2.90/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.96  
% 2.90/0.96  ------ Combination Options
% 2.90/0.96  
% 2.90/0.96  --comb_res_mult                         3
% 2.90/0.96  --comb_sup_mult                         2
% 2.90/0.96  --comb_inst_mult                        10
% 2.90/0.96  
% 2.90/0.96  ------ Debug Options
% 2.90/0.96  
% 2.90/0.96  --dbg_backtrace                         false
% 2.90/0.96  --dbg_dump_prop_clauses                 false
% 2.90/0.96  --dbg_dump_prop_clauses_file            -
% 2.90/0.96  --dbg_out_stat                          false
% 2.90/0.96  ------ Parsing...
% 2.90/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/0.96  ------ Proving...
% 2.90/0.96  ------ Problem Properties 
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  clauses                                 31
% 2.90/0.96  conjectures                             5
% 2.90/0.96  EPR                                     9
% 2.90/0.96  Horn                                    23
% 2.90/0.96  unary                                   9
% 2.90/0.96  binary                                  12
% 2.90/0.96  lits                                    73
% 2.90/0.96  lits eq                                 29
% 2.90/0.96  fd_pure                                 0
% 2.90/0.96  fd_pseudo                               0
% 2.90/0.96  fd_cond                                 1
% 2.90/0.96  fd_pseudo_cond                          4
% 2.90/0.96  AC symbols                              0
% 2.90/0.96  
% 2.90/0.96  ------ Schedule dynamic 5 is on 
% 2.90/0.96  
% 2.90/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  ------ 
% 2.90/0.96  Current options:
% 2.90/0.96  ------ 
% 2.90/0.96  
% 2.90/0.96  ------ Input Options
% 2.90/0.96  
% 2.90/0.96  --out_options                           all
% 2.90/0.96  --tptp_safe_out                         true
% 2.90/0.96  --problem_path                          ""
% 2.90/0.96  --include_path                          ""
% 2.90/0.96  --clausifier                            res/vclausify_rel
% 2.90/0.96  --clausifier_options                    --mode clausify
% 2.90/0.96  --stdin                                 false
% 2.90/0.96  --stats_out                             all
% 2.90/0.96  
% 2.90/0.96  ------ General Options
% 2.90/0.96  
% 2.90/0.96  --fof                                   false
% 2.90/0.96  --time_out_real                         305.
% 2.90/0.96  --time_out_virtual                      -1.
% 2.90/0.96  --symbol_type_check                     false
% 2.90/0.96  --clausify_out                          false
% 2.90/0.96  --sig_cnt_out                           false
% 2.90/0.96  --trig_cnt_out                          false
% 2.90/0.96  --trig_cnt_out_tolerance                1.
% 2.90/0.96  --trig_cnt_out_sk_spl                   false
% 2.90/0.96  --abstr_cl_out                          false
% 2.90/0.96  
% 2.90/0.96  ------ Global Options
% 2.90/0.96  
% 2.90/0.96  --schedule                              default
% 2.90/0.96  --add_important_lit                     false
% 2.90/0.96  --prop_solver_per_cl                    1000
% 2.90/0.96  --min_unsat_core                        false
% 2.90/0.96  --soft_assumptions                      false
% 2.90/0.96  --soft_lemma_size                       3
% 2.90/0.96  --prop_impl_unit_size                   0
% 2.90/0.96  --prop_impl_unit                        []
% 2.90/0.96  --share_sel_clauses                     true
% 2.90/0.96  --reset_solvers                         false
% 2.90/0.96  --bc_imp_inh                            [conj_cone]
% 2.90/0.96  --conj_cone_tolerance                   3.
% 2.90/0.96  --extra_neg_conj                        none
% 2.90/0.96  --large_theory_mode                     true
% 2.90/0.96  --prolific_symb_bound                   200
% 2.90/0.96  --lt_threshold                          2000
% 2.90/0.96  --clause_weak_htbl                      true
% 2.90/0.96  --gc_record_bc_elim                     false
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing Options
% 2.90/0.96  
% 2.90/0.96  --preprocessing_flag                    true
% 2.90/0.96  --time_out_prep_mult                    0.1
% 2.90/0.96  --splitting_mode                        input
% 2.90/0.96  --splitting_grd                         true
% 2.90/0.96  --splitting_cvd                         false
% 2.90/0.96  --splitting_cvd_svl                     false
% 2.90/0.96  --splitting_nvd                         32
% 2.90/0.96  --sub_typing                            true
% 2.90/0.96  --prep_gs_sim                           true
% 2.90/0.96  --prep_unflatten                        true
% 2.90/0.96  --prep_res_sim                          true
% 2.90/0.96  --prep_upred                            true
% 2.90/0.96  --prep_sem_filter                       exhaustive
% 2.90/0.96  --prep_sem_filter_out                   false
% 2.90/0.96  --pred_elim                             true
% 2.90/0.96  --res_sim_input                         true
% 2.90/0.96  --eq_ax_congr_red                       true
% 2.90/0.96  --pure_diseq_elim                       true
% 2.90/0.96  --brand_transform                       false
% 2.90/0.96  --non_eq_to_eq                          false
% 2.90/0.96  --prep_def_merge                        true
% 2.90/0.96  --prep_def_merge_prop_impl              false
% 2.90/0.96  --prep_def_merge_mbd                    true
% 2.90/0.96  --prep_def_merge_tr_red                 false
% 2.90/0.96  --prep_def_merge_tr_cl                  false
% 2.90/0.96  --smt_preprocessing                     true
% 2.90/0.96  --smt_ac_axioms                         fast
% 2.90/0.96  --preprocessed_out                      false
% 2.90/0.96  --preprocessed_stats                    false
% 2.90/0.96  
% 2.90/0.96  ------ Abstraction refinement Options
% 2.90/0.96  
% 2.90/0.96  --abstr_ref                             []
% 2.90/0.96  --abstr_ref_prep                        false
% 2.90/0.96  --abstr_ref_until_sat                   false
% 2.90/0.96  --abstr_ref_sig_restrict                funpre
% 2.90/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.96  --abstr_ref_under                       []
% 2.90/0.96  
% 2.90/0.96  ------ SAT Options
% 2.90/0.96  
% 2.90/0.96  --sat_mode                              false
% 2.90/0.96  --sat_fm_restart_options                ""
% 2.90/0.96  --sat_gr_def                            false
% 2.90/0.96  --sat_epr_types                         true
% 2.90/0.96  --sat_non_cyclic_types                  false
% 2.90/0.96  --sat_finite_models                     false
% 2.90/0.96  --sat_fm_lemmas                         false
% 2.90/0.96  --sat_fm_prep                           false
% 2.90/0.96  --sat_fm_uc_incr                        true
% 2.90/0.96  --sat_out_model                         small
% 2.90/0.96  --sat_out_clauses                       false
% 2.90/0.96  
% 2.90/0.96  ------ QBF Options
% 2.90/0.96  
% 2.90/0.96  --qbf_mode                              false
% 2.90/0.96  --qbf_elim_univ                         false
% 2.90/0.96  --qbf_dom_inst                          none
% 2.90/0.96  --qbf_dom_pre_inst                      false
% 2.90/0.96  --qbf_sk_in                             false
% 2.90/0.96  --qbf_pred_elim                         true
% 2.90/0.96  --qbf_split                             512
% 2.90/0.96  
% 2.90/0.96  ------ BMC1 Options
% 2.90/0.96  
% 2.90/0.96  --bmc1_incremental                      false
% 2.90/0.96  --bmc1_axioms                           reachable_all
% 2.90/0.96  --bmc1_min_bound                        0
% 2.90/0.96  --bmc1_max_bound                        -1
% 2.90/0.96  --bmc1_max_bound_default                -1
% 2.90/0.96  --bmc1_symbol_reachability              true
% 2.90/0.96  --bmc1_property_lemmas                  false
% 2.90/0.96  --bmc1_k_induction                      false
% 2.90/0.96  --bmc1_non_equiv_states                 false
% 2.90/0.96  --bmc1_deadlock                         false
% 2.90/0.96  --bmc1_ucm                              false
% 2.90/0.96  --bmc1_add_unsat_core                   none
% 2.90/0.96  --bmc1_unsat_core_children              false
% 2.90/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.96  --bmc1_out_stat                         full
% 2.90/0.96  --bmc1_ground_init                      false
% 2.90/0.96  --bmc1_pre_inst_next_state              false
% 2.90/0.96  --bmc1_pre_inst_state                   false
% 2.90/0.96  --bmc1_pre_inst_reach_state             false
% 2.90/0.96  --bmc1_out_unsat_core                   false
% 2.90/0.96  --bmc1_aig_witness_out                  false
% 2.90/0.96  --bmc1_verbose                          false
% 2.90/0.96  --bmc1_dump_clauses_tptp                false
% 2.90/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.96  --bmc1_dump_file                        -
% 2.90/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.96  --bmc1_ucm_extend_mode                  1
% 2.90/0.96  --bmc1_ucm_init_mode                    2
% 2.90/0.96  --bmc1_ucm_cone_mode                    none
% 2.90/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.96  --bmc1_ucm_relax_model                  4
% 2.90/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.96  --bmc1_ucm_layered_model                none
% 2.90/0.96  --bmc1_ucm_max_lemma_size               10
% 2.90/0.96  
% 2.90/0.96  ------ AIG Options
% 2.90/0.96  
% 2.90/0.96  --aig_mode                              false
% 2.90/0.96  
% 2.90/0.96  ------ Instantiation Options
% 2.90/0.96  
% 2.90/0.96  --instantiation_flag                    true
% 2.90/0.96  --inst_sos_flag                         false
% 2.90/0.96  --inst_sos_phase                        true
% 2.90/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.96  --inst_lit_sel_side                     none
% 2.90/0.96  --inst_solver_per_active                1400
% 2.90/0.96  --inst_solver_calls_frac                1.
% 2.90/0.96  --inst_passive_queue_type               priority_queues
% 2.90/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.96  --inst_passive_queues_freq              [25;2]
% 2.90/0.96  --inst_dismatching                      true
% 2.90/0.96  --inst_eager_unprocessed_to_passive     true
% 2.90/0.96  --inst_prop_sim_given                   true
% 2.90/0.96  --inst_prop_sim_new                     false
% 2.90/0.96  --inst_subs_new                         false
% 2.90/0.96  --inst_eq_res_simp                      false
% 2.90/0.96  --inst_subs_given                       false
% 2.90/0.96  --inst_orphan_elimination               true
% 2.90/0.96  --inst_learning_loop_flag               true
% 2.90/0.96  --inst_learning_start                   3000
% 2.90/0.96  --inst_learning_factor                  2
% 2.90/0.96  --inst_start_prop_sim_after_learn       3
% 2.90/0.96  --inst_sel_renew                        solver
% 2.90/0.96  --inst_lit_activity_flag                true
% 2.90/0.96  --inst_restr_to_given                   false
% 2.90/0.96  --inst_activity_threshold               500
% 2.90/0.96  --inst_out_proof                        true
% 2.90/0.96  
% 2.90/0.96  ------ Resolution Options
% 2.90/0.96  
% 2.90/0.96  --resolution_flag                       false
% 2.90/0.96  --res_lit_sel                           adaptive
% 2.90/0.96  --res_lit_sel_side                      none
% 2.90/0.96  --res_ordering                          kbo
% 2.90/0.96  --res_to_prop_solver                    active
% 2.90/0.96  --res_prop_simpl_new                    false
% 2.90/0.96  --res_prop_simpl_given                  true
% 2.90/0.96  --res_passive_queue_type                priority_queues
% 2.90/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.96  --res_passive_queues_freq               [15;5]
% 2.90/0.96  --res_forward_subs                      full
% 2.90/0.96  --res_backward_subs                     full
% 2.90/0.96  --res_forward_subs_resolution           true
% 2.90/0.96  --res_backward_subs_resolution          true
% 2.90/0.96  --res_orphan_elimination                true
% 2.90/0.96  --res_time_limit                        2.
% 2.90/0.96  --res_out_proof                         true
% 2.90/0.96  
% 2.90/0.96  ------ Superposition Options
% 2.90/0.96  
% 2.90/0.96  --superposition_flag                    true
% 2.90/0.96  --sup_passive_queue_type                priority_queues
% 2.90/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.96  --demod_completeness_check              fast
% 2.90/0.96  --demod_use_ground                      true
% 2.90/0.96  --sup_to_prop_solver                    passive
% 2.90/0.96  --sup_prop_simpl_new                    true
% 2.90/0.96  --sup_prop_simpl_given                  true
% 2.90/0.96  --sup_fun_splitting                     false
% 2.90/0.96  --sup_smt_interval                      50000
% 2.90/0.96  
% 2.90/0.96  ------ Superposition Simplification Setup
% 2.90/0.96  
% 2.90/0.96  --sup_indices_passive                   []
% 2.90/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_full_bw                           [BwDemod]
% 2.90/0.96  --sup_immed_triv                        [TrivRules]
% 2.90/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_immed_bw_main                     []
% 2.90/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.96  
% 2.90/0.96  ------ Combination Options
% 2.90/0.96  
% 2.90/0.96  --comb_res_mult                         3
% 2.90/0.96  --comb_sup_mult                         2
% 2.90/0.96  --comb_inst_mult                        10
% 2.90/0.96  
% 2.90/0.96  ------ Debug Options
% 2.90/0.96  
% 2.90/0.96  --dbg_backtrace                         false
% 2.90/0.96  --dbg_dump_prop_clauses                 false
% 2.90/0.96  --dbg_dump_prop_clauses_file            -
% 2.90/0.96  --dbg_out_stat                          false
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  ------ Proving...
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  % SZS status Theorem for theBenchmark.p
% 2.90/0.96  
% 2.90/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/0.96  
% 2.90/0.96  fof(f13,axiom,(
% 2.90/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f24,plain,(
% 2.90/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(ennf_transformation,[],[f13])).
% 2.90/0.96  
% 2.90/0.96  fof(f25,plain,(
% 2.90/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(flattening,[],[f24])).
% 2.90/0.96  
% 2.90/0.96  fof(f43,plain,(
% 2.90/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(nnf_transformation,[],[f25])).
% 2.90/0.96  
% 2.90/0.96  fof(f68,plain,(
% 2.90/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.96    inference(cnf_transformation,[],[f43])).
% 2.90/0.96  
% 2.90/0.96  fof(f14,conjecture,(
% 2.90/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f15,negated_conjecture,(
% 2.90/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.90/0.96    inference(negated_conjecture,[],[f14])).
% 2.90/0.96  
% 2.90/0.96  fof(f26,plain,(
% 2.90/0.96    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.90/0.96    inference(ennf_transformation,[],[f15])).
% 2.90/0.96  
% 2.90/0.96  fof(f27,plain,(
% 2.90/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.90/0.96    inference(flattening,[],[f26])).
% 2.90/0.96  
% 2.90/0.96  fof(f45,plain,(
% 2.90/0.96    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 2.90/0.96    introduced(choice_axiom,[])).
% 2.90/0.96  
% 2.90/0.96  fof(f44,plain,(
% 2.90/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 2.90/0.96    introduced(choice_axiom,[])).
% 2.90/0.96  
% 2.90/0.96  fof(f46,plain,(
% 2.90/0.96    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 2.90/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f45,f44])).
% 2.90/0.96  
% 2.90/0.96  fof(f78,plain,(
% 2.90/0.96    v1_funct_2(sK6,sK3,sK4)),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f79,plain,(
% 2.90/0.96    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f11,axiom,(
% 2.90/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f21,plain,(
% 2.90/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(ennf_transformation,[],[f11])).
% 2.90/0.96  
% 2.90/0.96  fof(f66,plain,(
% 2.90/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.96    inference(cnf_transformation,[],[f21])).
% 2.90/0.96  
% 2.90/0.96  fof(f75,plain,(
% 2.90/0.96    v1_funct_2(sK5,sK3,sK4)),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f76,plain,(
% 2.90/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f9,axiom,(
% 2.90/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f18,plain,(
% 2.90/0.96    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.96    inference(ennf_transformation,[],[f9])).
% 2.90/0.96  
% 2.90/0.96  fof(f19,plain,(
% 2.90/0.96    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.96    inference(flattening,[],[f18])).
% 2.90/0.96  
% 2.90/0.96  fof(f41,plain,(
% 2.90/0.96    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 2.90/0.96    introduced(choice_axiom,[])).
% 2.90/0.96  
% 2.90/0.96  fof(f42,plain,(
% 2.90/0.96    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f41])).
% 2.90/0.96  
% 2.90/0.96  fof(f63,plain,(
% 2.90/0.96    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.96    inference(cnf_transformation,[],[f42])).
% 2.90/0.96  
% 2.90/0.96  fof(f77,plain,(
% 2.90/0.96    v1_funct_1(sK6)),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f10,axiom,(
% 2.90/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f20,plain,(
% 2.90/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(ennf_transformation,[],[f10])).
% 2.90/0.96  
% 2.90/0.96  fof(f65,plain,(
% 2.90/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.96    inference(cnf_transformation,[],[f20])).
% 2.90/0.96  
% 2.90/0.96  fof(f74,plain,(
% 2.90/0.96    v1_funct_1(sK5)),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f12,axiom,(
% 2.90/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f22,plain,(
% 2.90/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.90/0.96    inference(ennf_transformation,[],[f12])).
% 2.90/0.96  
% 2.90/0.96  fof(f23,plain,(
% 2.90/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.96    inference(flattening,[],[f22])).
% 2.90/0.96  
% 2.90/0.96  fof(f67,plain,(
% 2.90/0.96    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.96    inference(cnf_transformation,[],[f23])).
% 2.90/0.96  
% 2.90/0.96  fof(f81,plain,(
% 2.90/0.96    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f80,plain,(
% 2.90/0.96    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 2.90/0.96    inference(cnf_transformation,[],[f46])).
% 2.90/0.96  
% 2.90/0.96  fof(f64,plain,(
% 2.90/0.96    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.96    inference(cnf_transformation,[],[f42])).
% 2.90/0.96  
% 2.90/0.96  fof(f7,axiom,(
% 2.90/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f38,plain,(
% 2.90/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.90/0.96    inference(nnf_transformation,[],[f7])).
% 2.90/0.96  
% 2.90/0.96  fof(f39,plain,(
% 2.90/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.90/0.96    inference(flattening,[],[f38])).
% 2.90/0.96  
% 2.90/0.96  fof(f60,plain,(
% 2.90/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.90/0.96    inference(cnf_transformation,[],[f39])).
% 2.90/0.96  
% 2.90/0.96  fof(f84,plain,(
% 2.90/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.90/0.96    inference(equality_resolution,[],[f60])).
% 2.90/0.96  
% 2.90/0.96  fof(f8,axiom,(
% 2.90/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f40,plain,(
% 2.90/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.90/0.96    inference(nnf_transformation,[],[f8])).
% 2.90/0.96  
% 2.90/0.96  fof(f61,plain,(
% 2.90/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.90/0.96    inference(cnf_transformation,[],[f40])).
% 2.90/0.96  
% 2.90/0.96  fof(f5,axiom,(
% 2.90/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f56,plain,(
% 2.90/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.90/0.96    inference(cnf_transformation,[],[f5])).
% 2.90/0.96  
% 2.90/0.96  fof(f4,axiom,(
% 2.90/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.96  
% 2.90/0.96  fof(f36,plain,(
% 2.90/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.90/0.96    inference(nnf_transformation,[],[f4])).
% 2.90/0.96  
% 2.90/0.96  fof(f37,plain,(
% 2.90/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.90/0.96    inference(flattening,[],[f36])).
% 2.90/0.96  
% 2.90/0.96  fof(f55,plain,(
% 2.90/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.90/0.96    inference(cnf_transformation,[],[f37])).
% 2.90/0.96  
% 2.90/0.96  cnf(c_26,plain,
% 2.90/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.96      | k1_xboole_0 = X2 ),
% 2.90/0.96      inference(cnf_transformation,[],[f68]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_30,negated_conjecture,
% 2.90/0.96      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.90/0.96      inference(cnf_transformation,[],[f78]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_510,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.96      | sK6 != X0
% 2.90/0.96      | sK4 != X2
% 2.90/0.96      | sK3 != X1
% 2.90/0.96      | k1_xboole_0 = X2 ),
% 2.90/0.96      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_511,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | k1_relset_1(sK3,sK4,sK6) = sK3
% 2.90/0.96      | k1_xboole_0 = sK4 ),
% 2.90/0.96      inference(unflattening,[status(thm)],[c_510]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_29,negated_conjecture,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.90/0.96      inference(cnf_transformation,[],[f79]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_513,plain,
% 2.90/0.96      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_511,c_29]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2036,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_19,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.90/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2038,plain,
% 2.90/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.90/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2419,plain,
% 2.90/0.96      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2036,c_2038]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2583,plain,
% 2.90/0.96      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_513,c_2419]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_33,negated_conjecture,
% 2.90/0.96      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.90/0.96      inference(cnf_transformation,[],[f75]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_521,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.96      | sK5 != X0
% 2.90/0.96      | sK4 != X2
% 2.90/0.96      | sK3 != X1
% 2.90/0.96      | k1_xboole_0 = X2 ),
% 2.90/0.96      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_522,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | k1_relset_1(sK3,sK4,sK5) = sK3
% 2.90/0.96      | k1_xboole_0 = sK4 ),
% 2.90/0.96      inference(unflattening,[status(thm)],[c_521]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_32,negated_conjecture,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.90/0.96      inference(cnf_transformation,[],[f76]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_524,plain,
% 2.90/0.96      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_522,c_32]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2034,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2420,plain,
% 2.90/0.96      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2034,c_2038]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2659,plain,
% 2.90/0.96      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_524,c_2420]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_17,plain,
% 2.90/0.96      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 2.90/0.96      | ~ v1_relat_1(X1)
% 2.90/0.96      | ~ v1_relat_1(X0)
% 2.90/0.96      | ~ v1_funct_1(X1)
% 2.90/0.96      | ~ v1_funct_1(X0)
% 2.90/0.96      | X1 = X0
% 2.90/0.96      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.90/0.96      inference(cnf_transformation,[],[f63]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2040,plain,
% 2.90/0.96      ( X0 = X1
% 2.90/0.96      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.90/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.90/0.96      | v1_relat_1(X1) != iProver_top
% 2.90/0.96      | v1_relat_1(X0) != iProver_top
% 2.90/0.96      | v1_funct_1(X0) != iProver_top
% 2.90/0.96      | v1_funct_1(X1) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3222,plain,
% 2.90/0.96      ( k1_relat_1(X0) != sK3
% 2.90/0.96      | sK6 = X0
% 2.90/0.96      | sK4 = k1_xboole_0
% 2.90/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.90/0.96      | v1_relat_1(X0) != iProver_top
% 2.90/0.96      | v1_relat_1(sK6) != iProver_top
% 2.90/0.96      | v1_funct_1(X0) != iProver_top
% 2.90/0.96      | v1_funct_1(sK6) != iProver_top ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2583,c_2040]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_31,negated_conjecture,
% 2.90/0.96      ( v1_funct_1(sK6) ),
% 2.90/0.96      inference(cnf_transformation,[],[f77]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_38,plain,
% 2.90/0.96      ( v1_funct_1(sK6) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_40,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_18,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | v1_relat_1(X0) ),
% 2.90/0.96      inference(cnf_transformation,[],[f65]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2283,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | v1_relat_1(sK6) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_18]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2284,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.90/0.96      | v1_relat_1(sK6) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2283]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3837,plain,
% 2.90/0.96      ( v1_funct_1(X0) != iProver_top
% 2.90/0.96      | k1_relat_1(X0) != sK3
% 2.90/0.96      | sK6 = X0
% 2.90/0.96      | sK4 = k1_xboole_0
% 2.90/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.90/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_3222,c_38,c_40,c_2284]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3838,plain,
% 2.90/0.96      ( k1_relat_1(X0) != sK3
% 2.90/0.96      | sK6 = X0
% 2.90/0.96      | sK4 = k1_xboole_0
% 2.90/0.96      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.90/0.96      | v1_relat_1(X0) != iProver_top
% 2.90/0.96      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.96      inference(renaming,[status(thm)],[c_3837]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3850,plain,
% 2.90/0.96      ( sK6 = sK5
% 2.90/0.96      | sK4 = k1_xboole_0
% 2.90/0.96      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.90/0.96      | v1_relat_1(sK5) != iProver_top
% 2.90/0.96      | v1_funct_1(sK5) != iProver_top ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2659,c_3838]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_34,negated_conjecture,
% 2.90/0.96      ( v1_funct_1(sK5) ),
% 2.90/0.96      inference(cnf_transformation,[],[f74]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_35,plain,
% 2.90/0.96      ( v1_funct_1(sK5) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_37,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_20,plain,
% 2.90/0.96      ( r2_relset_1(X0,X1,X2,X2)
% 2.90/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.90/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_27,negated_conjecture,
% 2.90/0.96      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 2.90/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_415,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.96      | sK6 != X0
% 2.90/0.96      | sK5 != X0
% 2.90/0.96      | sK4 != X2
% 2.90/0.96      | sK3 != X1 ),
% 2.90/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_416,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | sK5 != sK6 ),
% 2.90/0.96      inference(unflattening,[status(thm)],[c_415]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_420,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | sK5 != sK6 ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_416,c_29]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_744,plain,
% 2.90/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.90/0.96      | sK6 != X0
% 2.90/0.96      | sK6 != sK5 ),
% 2.90/0.96      inference(resolution_lifted,[status(thm)],[c_29,c_420]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_745,plain,
% 2.90/0.96      ( sK6 != sK5 ),
% 2.90/0.96      inference(unflattening,[status(thm)],[c_744]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2286,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.90/0.96      | v1_relat_1(sK5) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_18]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2287,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.90/0.96      | v1_relat_1(sK5) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2286]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3863,plain,
% 2.90/0.96      ( sK4 = k1_xboole_0
% 2.90/0.96      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_3850,c_35,c_37,c_745,c_2287]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3869,plain,
% 2.90/0.96      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2659,c_3863]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_28,negated_conjecture,
% 2.90/0.96      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 2.90/0.96      inference(cnf_transformation,[],[f80]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2037,plain,
% 2.90/0.96      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 2.90/0.96      | r2_hidden(X0,sK3) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_4093,plain,
% 2.90/0.96      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.90/0.96      | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_3869,c_2037]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_16,plain,
% 2.90/0.96      ( ~ v1_relat_1(X0)
% 2.90/0.96      | ~ v1_relat_1(X1)
% 2.90/0.96      | ~ v1_funct_1(X0)
% 2.90/0.96      | ~ v1_funct_1(X1)
% 2.90/0.96      | X0 = X1
% 2.90/0.96      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.90/0.96      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.90/0.96      inference(cnf_transformation,[],[f64]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2041,plain,
% 2.90/0.96      ( X0 = X1
% 2.90/0.96      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.90/0.96      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.90/0.96      | v1_relat_1(X0) != iProver_top
% 2.90/0.96      | v1_relat_1(X1) != iProver_top
% 2.90/0.96      | v1_funct_1(X1) != iProver_top
% 2.90/0.96      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_4254,plain,
% 2.90/0.96      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.90/0.96      | sK6 = sK5
% 2.90/0.96      | sK4 = k1_xboole_0
% 2.90/0.96      | v1_relat_1(sK6) != iProver_top
% 2.90/0.96      | v1_relat_1(sK5) != iProver_top
% 2.90/0.96      | v1_funct_1(sK6) != iProver_top
% 2.90/0.96      | v1_funct_1(sK5) != iProver_top ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_4093,c_2041]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_4270,plain,
% 2.90/0.96      ( ~ v1_relat_1(sK6)
% 2.90/0.96      | ~ v1_relat_1(sK5)
% 2.90/0.96      | ~ v1_funct_1(sK6)
% 2.90/0.96      | ~ v1_funct_1(sK5)
% 2.90/0.96      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.90/0.96      | sK6 = sK5
% 2.90/0.96      | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_4254]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5471,plain,
% 2.90/0.96      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_4254,c_34,c_32,c_31,c_29,c_745,c_2283,c_2286,c_4270]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5475,plain,
% 2.90/0.96      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(superposition,[status(thm)],[c_2583,c_5471]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5512,plain,
% 2.90/0.96      ( sK4 = k1_xboole_0 ),
% 2.90/0.96      inference(global_propositional_subsumption,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_5475,c_2659]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5534,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.90/0.96      inference(demodulation,[status(thm)],[c_5512,c_2036]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_11,plain,
% 2.90/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.90/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5540,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.90/0.96      inference(demodulation,[status(thm)],[c_5534,c_11]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5535,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 2.90/0.96      inference(demodulation,[status(thm)],[c_5512,c_2034]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_5537,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.90/0.96      inference(demodulation,[status(thm)],[c_5535,c_11]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_15,plain,
% 2.90/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.90/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3626,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0)) | r1_tarski(sK6,X0) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3627,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 2.90/0.96      | r1_tarski(sK6,X0) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_3626]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3629,plain,
% 2.90/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.90/0.96      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_3627]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3436,plain,
% 2.90/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3437,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 2.90/0.96      | r1_tarski(sK5,X0) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_3436]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3439,plain,
% 2.90/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.90/0.96      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_3437]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_9,plain,
% 2.90/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 2.90/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3421,plain,
% 2.90/0.96      ( r1_tarski(k1_xboole_0,sK6) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_9]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_3424,plain,
% 2.90/0.96      ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_3421]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_1393,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2381,plain,
% 2.90/0.96      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2786,plain,
% 2.90/0.96      ( sK6 != X0 | sK6 = sK5 | sK5 != X0 ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_2381]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2788,plain,
% 2.90/0.96      ( sK6 = sK5 | sK6 != k1_xboole_0 | sK5 != k1_xboole_0 ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_2786]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_6,plain,
% 2.90/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.90/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2665,plain,
% 2.90/0.96      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_6]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2671,plain,
% 2.90/0.96      ( sK5 = X0
% 2.90/0.96      | r1_tarski(X0,sK5) != iProver_top
% 2.90/0.96      | r1_tarski(sK5,X0) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2665]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2673,plain,
% 2.90/0.96      ( sK5 = k1_xboole_0
% 2.90/0.96      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.90/0.96      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_2671]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2647,plain,
% 2.90/0.96      ( r1_tarski(k1_xboole_0,sK5) ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_9]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2650,plain,
% 2.90/0.96      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2587,plain,
% 2.90/0.96      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_6]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2593,plain,
% 2.90/0.96      ( sK6 = X0
% 2.90/0.96      | r1_tarski(X0,sK6) != iProver_top
% 2.90/0.96      | r1_tarski(sK6,X0) != iProver_top ),
% 2.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(c_2595,plain,
% 2.90/0.96      ( sK6 = k1_xboole_0
% 2.90/0.96      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 2.90/0.96      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 2.90/0.96      inference(instantiation,[status(thm)],[c_2593]) ).
% 2.90/0.96  
% 2.90/0.96  cnf(contradiction,plain,
% 2.90/0.96      ( $false ),
% 2.90/0.96      inference(minisat,
% 2.90/0.96                [status(thm)],
% 2.90/0.96                [c_5540,c_5537,c_3629,c_3439,c_3424,c_2788,c_2673,c_2650,
% 2.90/0.96                 c_2595,c_745]) ).
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/0.96  
% 2.90/0.96  ------                               Statistics
% 2.90/0.96  
% 2.90/0.96  ------ General
% 2.90/0.96  
% 2.90/0.96  abstr_ref_over_cycles:                  0
% 2.90/0.96  abstr_ref_under_cycles:                 0
% 2.90/0.96  gc_basic_clause_elim:                   0
% 2.90/0.96  forced_gc_time:                         0
% 2.90/0.96  parsing_time:                           0.008
% 2.90/0.96  unif_index_cands_time:                  0.
% 2.90/0.96  unif_index_add_time:                    0.
% 2.90/0.96  orderings_time:                         0.
% 2.90/0.96  out_proof_time:                         0.011
% 2.90/0.96  total_time:                             0.181
% 2.90/0.96  num_of_symbols:                         52
% 2.90/0.96  num_of_terms:                           3560
% 2.90/0.96  
% 2.90/0.96  ------ Preprocessing
% 2.90/0.96  
% 2.90/0.96  num_of_splits:                          0
% 2.90/0.96  num_of_split_atoms:                     0
% 2.90/0.96  num_of_reused_defs:                     0
% 2.90/0.96  num_eq_ax_congr_red:                    26
% 2.90/0.96  num_of_sem_filtered_clauses:            1
% 2.90/0.96  num_of_subtypes:                        0
% 2.90/0.96  monotx_restored_types:                  0
% 2.90/0.96  sat_num_of_epr_types:                   0
% 2.90/0.96  sat_num_of_non_cyclic_types:            0
% 2.90/0.96  sat_guarded_non_collapsed_types:        0
% 2.90/0.96  num_pure_diseq_elim:                    0
% 2.90/0.96  simp_replaced_by:                       0
% 2.90/0.96  res_preprocessed:                       150
% 2.90/0.96  prep_upred:                             0
% 2.90/0.96  prep_unflattend:                        67
% 2.90/0.96  smt_new_axioms:                         0
% 2.90/0.96  pred_elim_cands:                        6
% 2.90/0.96  pred_elim:                              2
% 2.90/0.96  pred_elim_cl:                           3
% 2.90/0.96  pred_elim_cycles:                       4
% 2.90/0.96  merged_defs:                            8
% 2.90/0.96  merged_defs_ncl:                        0
% 2.90/0.96  bin_hyper_res:                          8
% 2.90/0.96  prep_cycles:                            4
% 2.90/0.96  pred_elim_time:                         0.021
% 2.90/0.96  splitting_time:                         0.
% 2.90/0.96  sem_filter_time:                        0.
% 2.90/0.96  monotx_time:                            0.001
% 2.90/0.96  subtype_inf_time:                       0.
% 2.90/0.96  
% 2.90/0.96  ------ Problem properties
% 2.90/0.96  
% 2.90/0.96  clauses:                                31
% 2.90/0.96  conjectures:                            5
% 2.90/0.96  epr:                                    9
% 2.90/0.96  horn:                                   23
% 2.90/0.96  ground:                                 11
% 2.90/0.96  unary:                                  9
% 2.90/0.96  binary:                                 12
% 2.90/0.96  lits:                                   73
% 2.90/0.96  lits_eq:                                29
% 2.90/0.96  fd_pure:                                0
% 2.90/0.96  fd_pseudo:                              0
% 2.90/0.96  fd_cond:                                1
% 2.90/0.96  fd_pseudo_cond:                         4
% 2.90/0.96  ac_symbols:                             0
% 2.90/0.96  
% 2.90/0.96  ------ Propositional Solver
% 2.90/0.96  
% 2.90/0.96  prop_solver_calls:                      28
% 2.90/0.96  prop_fast_solver_calls:                 1074
% 2.90/0.96  smt_solver_calls:                       0
% 2.90/0.96  smt_fast_solver_calls:                  0
% 2.90/0.96  prop_num_of_clauses:                    1612
% 2.90/0.96  prop_preprocess_simplified:             5602
% 2.90/0.96  prop_fo_subsumed:                       23
% 2.90/0.96  prop_solver_time:                       0.
% 2.90/0.96  smt_solver_time:                        0.
% 2.90/0.96  smt_fast_solver_time:                   0.
% 2.90/0.96  prop_fast_solver_time:                  0.
% 2.90/0.96  prop_unsat_core_time:                   0.
% 2.90/0.96  
% 2.90/0.96  ------ QBF
% 2.90/0.96  
% 2.90/0.96  qbf_q_res:                              0
% 2.90/0.96  qbf_num_tautologies:                    0
% 2.90/0.96  qbf_prep_cycles:                        0
% 2.90/0.96  
% 2.90/0.96  ------ BMC1
% 2.90/0.96  
% 2.90/0.96  bmc1_current_bound:                     -1
% 2.90/0.96  bmc1_last_solved_bound:                 -1
% 2.90/0.96  bmc1_unsat_core_size:                   -1
% 2.90/0.96  bmc1_unsat_core_parents_size:           -1
% 2.90/0.96  bmc1_merge_next_fun:                    0
% 2.90/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.90/0.96  
% 2.90/0.96  ------ Instantiation
% 2.90/0.96  
% 2.90/0.96  inst_num_of_clauses:                    470
% 2.90/0.96  inst_num_in_passive:                    121
% 2.90/0.96  inst_num_in_active:                     255
% 2.90/0.96  inst_num_in_unprocessed:                94
% 2.90/0.96  inst_num_of_loops:                      340
% 2.90/0.96  inst_num_of_learning_restarts:          0
% 2.90/0.96  inst_num_moves_active_passive:          82
% 2.90/0.96  inst_lit_activity:                      0
% 2.90/0.96  inst_lit_activity_moves:                0
% 2.90/0.96  inst_num_tautologies:                   0
% 2.90/0.96  inst_num_prop_implied:                  0
% 2.90/0.96  inst_num_existing_simplified:           0
% 2.90/0.96  inst_num_eq_res_simplified:             0
% 2.90/0.96  inst_num_child_elim:                    0
% 2.90/0.96  inst_num_of_dismatching_blockings:      106
% 2.90/0.96  inst_num_of_non_proper_insts:           509
% 2.90/0.96  inst_num_of_duplicates:                 0
% 2.90/0.96  inst_inst_num_from_inst_to_res:         0
% 2.90/0.96  inst_dismatching_checking_time:         0.
% 2.90/0.96  
% 2.90/0.96  ------ Resolution
% 2.90/0.96  
% 2.90/0.96  res_num_of_clauses:                     0
% 2.90/0.96  res_num_in_passive:                     0
% 2.90/0.96  res_num_in_active:                      0
% 2.90/0.96  res_num_of_loops:                       154
% 2.90/0.96  res_forward_subset_subsumed:            39
% 2.90/0.96  res_backward_subset_subsumed:           0
% 2.90/0.96  res_forward_subsumed:                   0
% 2.90/0.96  res_backward_subsumed:                  1
% 2.90/0.96  res_forward_subsumption_resolution:     0
% 2.90/0.96  res_backward_subsumption_resolution:    0
% 2.90/0.96  res_clause_to_clause_subsumption:       234
% 2.90/0.96  res_orphan_elimination:                 0
% 2.90/0.96  res_tautology_del:                      80
% 2.90/0.96  res_num_eq_res_simplified:              0
% 2.90/0.96  res_num_sel_changes:                    0
% 2.90/0.96  res_moves_from_active_to_pass:          0
% 2.90/0.96  
% 2.90/0.96  ------ Superposition
% 2.90/0.96  
% 2.90/0.96  sup_time_total:                         0.
% 2.90/0.96  sup_time_generating:                    0.
% 2.90/0.96  sup_time_sim_full:                      0.
% 2.90/0.96  sup_time_sim_immed:                     0.
% 2.90/0.96  
% 2.90/0.96  sup_num_of_clauses:                     64
% 2.90/0.96  sup_num_in_active:                      39
% 2.90/0.96  sup_num_in_passive:                     25
% 2.90/0.96  sup_num_of_loops:                       66
% 2.90/0.96  sup_fw_superposition:                   57
% 2.90/0.96  sup_bw_superposition:                   23
% 2.90/0.96  sup_immediate_simplified:               12
% 2.90/0.96  sup_given_eliminated:                   0
% 2.90/0.96  comparisons_done:                       0
% 2.90/0.96  comparisons_avoided:                    18
% 2.90/0.96  
% 2.90/0.96  ------ Simplifications
% 2.90/0.96  
% 2.90/0.96  
% 2.90/0.96  sim_fw_subset_subsumed:                 1
% 2.90/0.96  sim_bw_subset_subsumed:                 7
% 2.90/0.96  sim_fw_subsumed:                        0
% 2.90/0.96  sim_bw_subsumed:                        0
% 2.90/0.96  sim_fw_subsumption_res:                 4
% 2.90/0.96  sim_bw_subsumption_res:                 0
% 2.90/0.96  sim_tautology_del:                      3
% 2.90/0.96  sim_eq_tautology_del:                   18
% 2.90/0.96  sim_eq_res_simp:                        2
% 2.90/0.96  sim_fw_demodulated:                     13
% 2.90/0.96  sim_bw_demodulated:                     21
% 2.90/0.96  sim_light_normalised:                   0
% 2.90/0.96  sim_joinable_taut:                      0
% 2.90/0.96  sim_joinable_simp:                      0
% 2.90/0.96  sim_ac_normalised:                      0
% 2.90/0.96  sim_smt_subsumption:                    0
% 2.90/0.96  
%------------------------------------------------------------------------------
