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
% DateTime   : Thu Dec  3 12:07:40 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  159 (1064 expanded)
%              Number of clauses        :   99 ( 386 expanded)
%              Number of leaves         :   21 ( 267 expanded)
%              Depth                    :   23
%              Number of atoms          :  530 (6141 expanded)
%              Number of equality atoms :  233 (1278 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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
                ( m1_subset_1(X4,X0)
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
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f39,f38])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_567,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_569,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_26])).

cnf(c_1141,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1145,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2021,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1141,c_1145])).

cnf(c_2340,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_569,c_2021])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1316,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1422,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1424,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_774,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1505,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1507,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_1143,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2096,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1146])).

cnf(c_2106,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2096])).

cnf(c_2097,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1146])).

cnf(c_2107,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2097])).

cnf(c_775,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1834,plain,
    ( X0 != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_2769,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_772,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2770,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1378,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_2888,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0 != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_2891,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2888])).

cnf(c_2961,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_23,c_0,c_388,c_1316,c_1424,c_1507,c_2106,c_2107,c_2769,c_2770,c_2891])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_558,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_23])).

cnf(c_2020,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1143,c_1145])).

cnf(c_2288,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_558,c_2020])).

cnf(c_2914,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2288,c_23,c_0,c_388,c_1316,c_1424,c_1507,c_2106,c_2107,c_2769,c_2770,c_2891])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1148,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2924,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(sK4,X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2914,c_1148])).

cnf(c_2947,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2924,c_2914])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1334,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_3164,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_32,c_34,c_1334])).

cnf(c_3165,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3164])).

cnf(c_3176,plain,
    ( sK4 = sK3
    | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_3165])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1337,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_1484,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_773,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1361,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1760,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_23])).

cnf(c_3135,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_3601,plain,
    ( r2_hidden(sK0(sK4,sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3176,c_29,c_31,c_23,c_1337,c_1484,c_1760,c_3135])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_406,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_7])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_11,c_10,c_7])).

cnf(c_411,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_428,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_411])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_2003,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1138])).

cnf(c_2918,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2914,c_2003])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1150,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3038,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | m1_subset_1(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_1150])).

cnf(c_3606,plain,
    ( m1_subset_1(sK0(sK4,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_3038])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1144,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4159,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_3606,c_1144])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1149,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4161,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4159,c_1149])).

cnf(c_4162,plain,
    ( sK4 = sK3
    | sK1 != sK1
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4161,c_2914,c_2961])).

cnf(c_4163,plain,
    ( sK4 = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4163,c_3135,c_1760,c_1484,c_1337,c_1334,c_34,c_23,c_32,c_31,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.40/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.99  
% 2.40/0.99  ------  iProver source info
% 2.40/0.99  
% 2.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.99  git: non_committed_changes: false
% 2.40/0.99  git: last_make_outside_of_git: false
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     num_symb
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       true
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  ------ Parsing...
% 2.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.99  ------ Proving...
% 2.40/0.99  ------ Problem Properties 
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  clauses                                 22
% 2.40/0.99  conjectures                             5
% 2.40/0.99  EPR                                     4
% 2.40/0.99  Horn                                    17
% 2.40/0.99  unary                                   6
% 2.40/0.99  binary                                  7
% 2.40/0.99  lits                                    57
% 2.40/0.99  lits eq                                 23
% 2.40/0.99  fd_pure                                 0
% 2.40/0.99  fd_pseudo                               0
% 2.40/0.99  fd_cond                                 0
% 2.40/0.99  fd_pseudo_cond                          3
% 2.40/0.99  AC symbols                              0
% 2.40/0.99  
% 2.40/0.99  ------ Schedule dynamic 5 is on 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  Current options:
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     none
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       false
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ Proving...
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS status Theorem for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  fof(f13,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f29,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(ennf_transformation,[],[f13])).
% 2.40/0.99  
% 2.40/0.99  fof(f30,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(flattening,[],[f29])).
% 2.40/0.99  
% 2.40/0.99  fof(f37,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(nnf_transformation,[],[f30])).
% 2.40/0.99  
% 2.40/0.99  fof(f56,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f37])).
% 2.40/0.99  
% 2.40/0.99  fof(f14,conjecture,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f15,negated_conjecture,(
% 2.40/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.40/0.99    inference(negated_conjecture,[],[f14])).
% 2.40/0.99  
% 2.40/0.99  fof(f31,plain,(
% 2.40/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.40/0.99    inference(ennf_transformation,[],[f15])).
% 2.40/0.99  
% 2.40/0.99  fof(f32,plain,(
% 2.40/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.40/0.99    inference(flattening,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f39,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f38,plain,(
% 2.40/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f40,plain,(
% 2.40/0.99    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f39,f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f63,plain,(
% 2.40/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f64,plain,(
% 2.40/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f11,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f26,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(ennf_transformation,[],[f11])).
% 2.40/0.99  
% 2.40/0.99  fof(f54,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f26])).
% 2.40/0.99  
% 2.40/0.99  fof(f67,plain,(
% 2.40/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f1,axiom,(
% 2.40/0.99    v1_xboole_0(k1_xboole_0)),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f41,plain,(
% 2.40/0.99    v1_xboole_0(k1_xboole_0)),
% 2.40/0.99    inference(cnf_transformation,[],[f1])).
% 2.40/0.99  
% 2.40/0.99  fof(f12,axiom,(
% 2.40/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f27,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.40/0.99    inference(ennf_transformation,[],[f12])).
% 2.40/0.99  
% 2.40/0.99  fof(f28,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(flattening,[],[f27])).
% 2.40/0.99  
% 2.40/0.99  fof(f55,plain,(
% 2.40/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f28])).
% 2.40/0.99  
% 2.40/0.99  fof(f69,plain,(
% 2.40/0.99    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f2,axiom,(
% 2.40/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f17,plain,(
% 2.40/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f2])).
% 2.40/0.99  
% 2.40/0.99  fof(f42,plain,(
% 2.40/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f17])).
% 2.40/0.99  
% 2.40/0.99  fof(f10,axiom,(
% 2.40/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f25,plain,(
% 2.40/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f10])).
% 2.40/0.99  
% 2.40/0.99  fof(f53,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f25])).
% 2.40/0.99  
% 2.40/0.99  fof(f66,plain,(
% 2.40/0.99    v1_funct_2(sK4,sK1,sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f7,axiom,(
% 2.40/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f21,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f7])).
% 2.40/0.99  
% 2.40/0.99  fof(f22,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.40/0.99    inference(flattening,[],[f21])).
% 2.40/0.99  
% 2.40/0.99  fof(f35,plain,(
% 2.40/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f36,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).
% 2.40/0.99  
% 2.40/0.99  fof(f49,plain,(
% 2.40/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f36])).
% 2.40/0.99  
% 2.40/0.99  fof(f65,plain,(
% 2.40/0.99    v1_funct_1(sK4)),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f8,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f23,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(ennf_transformation,[],[f8])).
% 2.40/0.99  
% 2.40/0.99  fof(f51,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f23])).
% 2.40/0.99  
% 2.40/0.99  fof(f62,plain,(
% 2.40/0.99    v1_funct_1(sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f4,axiom,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f33,plain,(
% 2.40/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/0.99    inference(nnf_transformation,[],[f4])).
% 2.40/0.99  
% 2.40/0.99  fof(f45,plain,(
% 2.40/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f9,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f16,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.40/0.99  
% 2.40/0.99  fof(f24,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.99    inference(ennf_transformation,[],[f16])).
% 2.40/0.99  
% 2.40/0.99  fof(f52,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f24])).
% 2.40/0.99  
% 2.40/0.99  fof(f6,axiom,(
% 2.40/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f20,plain,(
% 2.40/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.99    inference(ennf_transformation,[],[f6])).
% 2.40/0.99  
% 2.40/0.99  fof(f34,plain,(
% 2.40/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.40/0.99    inference(nnf_transformation,[],[f20])).
% 2.40/0.99  
% 2.40/0.99  fof(f47,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f34])).
% 2.40/0.99  
% 2.40/0.99  fof(f5,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f18,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.40/0.99    inference(ennf_transformation,[],[f5])).
% 2.40/0.99  
% 2.40/0.99  fof(f19,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.40/0.99    inference(flattening,[],[f18])).
% 2.40/0.99  
% 2.40/0.99  fof(f46,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f19])).
% 2.40/0.99  
% 2.40/0.99  fof(f68,plain,(
% 2.40/0.99    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f50,plain,(
% 2.40/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f36])).
% 2.40/0.99  
% 2.40/0.99  cnf(c_20,plain,
% 2.40/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.40/0.99      | k1_xboole_0 = X2 ),
% 2.40/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_27,negated_conjecture,
% 2.40/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.40/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_566,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.40/0.99      | sK3 != X0
% 2.40/0.99      | sK2 != X2
% 2.40/0.99      | sK1 != X1
% 2.40/0.99      | k1_xboole_0 = X2 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_567,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.40/0.99      | k1_xboole_0 = sK2 ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_566]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_26,negated_conjecture,
% 2.40/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_569,plain,
% 2.40/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_567,c_26]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1141,plain,
% 2.40/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_13,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1145,plain,
% 2.40/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.40/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2021,plain,
% 2.40/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1141,c_1145]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2340,plain,
% 2.40/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_569,c_2021]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_23,negated_conjecture,
% 2.40/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_0,plain,
% 2.40/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_14,plain,
% 2.40/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.40/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_21,negated_conjecture,
% 2.40/0.99      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 2.40/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_385,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | sK4 != X0
% 2.40/0.99      | sK3 != X0
% 2.40/0.99      | sK2 != X2
% 2.40/0.99      | sK1 != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_386,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | sK3 != sK4 ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_388,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | sK3 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_386]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1,plain,
% 2.40/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.40/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1316,plain,
% 2.40/0.99      ( ~ v1_xboole_0(sK4) | ~ v1_xboole_0(sK3) | sK3 = sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1422,plain,
% 2.40/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK4) | X0 = sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1424,plain,
% 2.40/0.99      ( ~ v1_xboole_0(sK4)
% 2.40/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.40/0.99      | k1_xboole_0 = sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1422]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_774,plain,
% 2.40/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1505,plain,
% 2.40/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_774]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1507,plain,
% 2.40/0.99      ( v1_xboole_0(sK2)
% 2.40/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.40/0.99      | sK2 != k1_xboole_0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1505]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1143,plain,
% 2.40/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_12,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | ~ v1_xboole_0(X2)
% 2.40/0.99      | v1_xboole_0(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1146,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.40/0.99      | v1_xboole_0(X2) != iProver_top
% 2.40/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2096,plain,
% 2.40/0.99      ( v1_xboole_0(sK4) = iProver_top
% 2.40/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1143,c_1146]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2106,plain,
% 2.40/0.99      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 2.40/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2096]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2097,plain,
% 2.40/0.99      ( v1_xboole_0(sK3) = iProver_top
% 2.40/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1141,c_1146]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2107,plain,
% 2.40/0.99      ( v1_xboole_0(sK3) | ~ v1_xboole_0(sK2) ),
% 2.40/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2097]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_775,plain,
% 2.40/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1834,plain,
% 2.40/0.99      ( X0 != k2_zfmisc_1(sK1,sK2)
% 2.40/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_775]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2769,plain,
% 2.40/0.99      ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2)
% 2.40/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1834]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_772,plain,( X0 = X0 ),theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2770,plain,
% 2.40/0.99      ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_772]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_776,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1378,plain,
% 2.40/0.99      ( m1_subset_1(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.40/0.99      | X0 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_776]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2888,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | X0 != sK4
% 2.40/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2891,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.40/0.99      | k1_xboole_0 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2888]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2961,plain,
% 2.40/0.99      ( k1_relat_1(sK3) = sK1 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_2340,c_23,c_0,c_388,c_1316,c_1424,c_1507,c_2106,
% 2.40/0.99                 c_2107,c_2769,c_2770,c_2891]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_24,negated_conjecture,
% 2.40/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.40/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_555,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.40/0.99      | sK4 != X0
% 2.40/0.99      | sK2 != X2
% 2.40/0.99      | sK1 != X1
% 2.40/0.99      | k1_xboole_0 = X2 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_556,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.40/0.99      | k1_xboole_0 = sK2 ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_558,plain,
% 2.40/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_556,c_23]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2020,plain,
% 2.40/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1143,c_1145]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2288,plain,
% 2.40/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_558,c_2020]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2914,plain,
% 2.40/0.99      ( k1_relat_1(sK4) = sK1 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_2288,c_23,c_0,c_388,c_1316,c_1424,c_1507,c_2106,
% 2.40/0.99                 c_2107,c_2769,c_2770,c_2891]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_9,plain,
% 2.40/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.40/0.99      | ~ v1_funct_1(X1)
% 2.40/0.99      | ~ v1_funct_1(X0)
% 2.40/0.99      | ~ v1_relat_1(X1)
% 2.40/0.99      | ~ v1_relat_1(X0)
% 2.40/0.99      | X0 = X1
% 2.40/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1148,plain,
% 2.40/0.99      ( X0 = X1
% 2.40/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.40/0.99      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.40/0.99      | v1_funct_1(X1) != iProver_top
% 2.40/0.99      | v1_funct_1(X0) != iProver_top
% 2.40/0.99      | v1_relat_1(X0) != iProver_top
% 2.40/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2924,plain,
% 2.40/0.99      ( k1_relat_1(X0) != sK1
% 2.40/0.99      | sK4 = X0
% 2.40/0.99      | r2_hidden(sK0(sK4,X0),k1_relat_1(sK4)) = iProver_top
% 2.40/0.99      | v1_funct_1(X0) != iProver_top
% 2.40/0.99      | v1_funct_1(sK4) != iProver_top
% 2.40/0.99      | v1_relat_1(X0) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_2914,c_1148]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2947,plain,
% 2.40/0.99      ( k1_relat_1(X0) != sK1
% 2.40/0.99      | sK4 = X0
% 2.40/0.99      | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
% 2.40/0.99      | v1_funct_1(X0) != iProver_top
% 2.40/0.99      | v1_funct_1(sK4) != iProver_top
% 2.40/0.99      | v1_relat_1(X0) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.40/0.99      inference(light_normalisation,[status(thm)],[c_2924,c_2914]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_25,negated_conjecture,
% 2.40/0.99      ( v1_funct_1(sK4) ),
% 2.40/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_32,plain,
% 2.40/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_34,plain,
% 2.40/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_10,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | v1_relat_1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1333,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | v1_relat_1(sK4) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1334,plain,
% 2.40/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3164,plain,
% 2.40/0.99      ( v1_relat_1(X0) != iProver_top
% 2.40/0.99      | k1_relat_1(X0) != sK1
% 2.40/0.99      | sK4 = X0
% 2.40/0.99      | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
% 2.40/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_2947,c_32,c_34,c_1334]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3165,plain,
% 2.40/0.99      ( k1_relat_1(X0) != sK1
% 2.40/0.99      | sK4 = X0
% 2.40/0.99      | r2_hidden(sK0(sK4,X0),sK1) = iProver_top
% 2.40/0.99      | v1_funct_1(X0) != iProver_top
% 2.40/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_3164]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3176,plain,
% 2.40/0.99      ( sK4 = sK3
% 2.40/0.99      | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
% 2.40/0.99      | v1_funct_1(sK3) != iProver_top
% 2.40/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_2961,c_3165]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_28,negated_conjecture,
% 2.40/0.99      ( v1_funct_1(sK3) ),
% 2.40/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_29,plain,
% 2.40/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_31,plain,
% 2.40/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1336,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | v1_relat_1(sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1337,plain,
% 2.40/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.40/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1484,plain,
% 2.40/0.99      ( sK3 = sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_772]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_773,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1361,plain,
% 2.40/0.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_773]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1760,plain,
% 2.40/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1361]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_390,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | sK3 != sK4 ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_386,c_23]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3135,plain,
% 2.40/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.40/0.99      | sK3 != sK4 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_390]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3601,plain,
% 2.40/0.99      ( r2_hidden(sK0(sK4,sK3),sK1) = iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_3176,c_29,c_31,c_23,c_1337,c_1484,c_1760,c_3135]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_222,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.40/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_11,plain,
% 2.40/0.99      ( v4_relat_1(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_7,plain,
% 2.40/0.99      ( ~ v4_relat_1(X0,X1)
% 2.40/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.99      | ~ v1_relat_1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_406,plain,
% 2.40/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | ~ v1_relat_1(X0) ),
% 2.40/0.99      inference(resolution,[status(thm)],[c_11,c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_410,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_406,c_11,c_10,c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_411,plain,
% 2.40/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_410]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_428,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.40/0.99      | X3 != X1
% 2.40/0.99      | k1_relat_1(X2) != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_222,c_411]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_429,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1138,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.40/0.99      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2003,plain,
% 2.40/0.99      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1143,c_1138]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2918,plain,
% 2.40/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_2914,c_2003]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1)
% 2.40/0.99      | m1_subset_1(X0,X2)
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1150,plain,
% 2.40/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,X2) = iProver_top
% 2.40/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3038,plain,
% 2.40/0.99      ( r2_hidden(X0,sK1) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,sK1) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_2918,c_1150]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3606,plain,
% 2.40/0.99      ( m1_subset_1(sK0(sK4,sK3),sK1) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_3601,c_3038]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_22,negated_conjecture,
% 2.40/0.99      ( ~ m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1144,plain,
% 2.40/0.99      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.40/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4159,plain,
% 2.40/0.99      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_3606,c_1144]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_8,plain,
% 2.40/0.99      ( ~ v1_funct_1(X0)
% 2.40/0.99      | ~ v1_funct_1(X1)
% 2.40/0.99      | ~ v1_relat_1(X0)
% 2.40/0.99      | ~ v1_relat_1(X1)
% 2.40/0.99      | X1 = X0
% 2.40/0.99      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.40/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1149,plain,
% 2.40/0.99      ( X0 = X1
% 2.40/0.99      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 2.40/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.40/0.99      | v1_funct_1(X0) != iProver_top
% 2.40/0.99      | v1_funct_1(X1) != iProver_top
% 2.40/0.99      | v1_relat_1(X1) != iProver_top
% 2.40/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4161,plain,
% 2.40/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.40/0.99      | sK4 = sK3
% 2.40/0.99      | v1_funct_1(sK4) != iProver_top
% 2.40/0.99      | v1_funct_1(sK3) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) != iProver_top
% 2.40/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_4159,c_1149]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4162,plain,
% 2.40/0.99      ( sK4 = sK3
% 2.40/0.99      | sK1 != sK1
% 2.40/0.99      | v1_funct_1(sK4) != iProver_top
% 2.40/0.99      | v1_funct_1(sK3) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) != iProver_top
% 2.40/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.40/0.99      inference(light_normalisation,[status(thm)],[c_4161,c_2914,c_2961]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4163,plain,
% 2.40/0.99      ( sK4 = sK3
% 2.40/0.99      | v1_funct_1(sK4) != iProver_top
% 2.40/0.99      | v1_funct_1(sK3) != iProver_top
% 2.40/0.99      | v1_relat_1(sK4) != iProver_top
% 2.40/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.40/0.99      inference(equality_resolution_simp,[status(thm)],[c_4162]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(contradiction,plain,
% 2.40/0.99      ( $false ),
% 2.40/0.99      inference(minisat,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_4163,c_3135,c_1760,c_1484,c_1337,c_1334,c_34,c_23,
% 2.40/0.99                 c_32,c_31,c_29]) ).
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  ------                               Statistics
% 2.40/0.99  
% 2.40/0.99  ------ General
% 2.40/0.99  
% 2.40/0.99  abstr_ref_over_cycles:                  0
% 2.40/0.99  abstr_ref_under_cycles:                 0
% 2.40/0.99  gc_basic_clause_elim:                   0
% 2.40/0.99  forced_gc_time:                         0
% 2.40/0.99  parsing_time:                           0.014
% 2.40/0.99  unif_index_cands_time:                  0.
% 2.40/0.99  unif_index_add_time:                    0.
% 2.40/0.99  orderings_time:                         0.
% 2.40/0.99  out_proof_time:                         0.015
% 2.40/0.99  total_time:                             0.153
% 2.40/0.99  num_of_symbols:                         51
% 2.40/0.99  num_of_terms:                           2831
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing
% 2.40/0.99  
% 2.40/0.99  num_of_splits:                          0
% 2.40/0.99  num_of_split_atoms:                     0
% 2.40/0.99  num_of_reused_defs:                     0
% 2.40/0.99  num_eq_ax_congr_red:                    17
% 2.40/0.99  num_of_sem_filtered_clauses:            1
% 2.40/0.99  num_of_subtypes:                        0
% 2.40/0.99  monotx_restored_types:                  0
% 2.40/0.99  sat_num_of_epr_types:                   0
% 2.40/0.99  sat_num_of_non_cyclic_types:            0
% 2.40/0.99  sat_guarded_non_collapsed_types:        0
% 2.40/0.99  num_pure_diseq_elim:                    0
% 2.40/0.99  simp_replaced_by:                       0
% 2.40/0.99  res_preprocessed:                       116
% 2.40/0.99  prep_upred:                             0
% 2.40/0.99  prep_unflattend:                        43
% 2.40/0.99  smt_new_axioms:                         0
% 2.40/0.99  pred_elim_cands:                        5
% 2.40/0.99  pred_elim:                              4
% 2.40/0.99  pred_elim_cl:                           7
% 2.40/0.99  pred_elim_cycles:                       7
% 2.40/0.99  merged_defs:                            2
% 2.40/0.99  merged_defs_ncl:                        0
% 2.40/0.99  bin_hyper_res:                          2
% 2.40/0.99  prep_cycles:                            4
% 2.40/0.99  pred_elim_time:                         0.006
% 2.40/0.99  splitting_time:                         0.
% 2.40/0.99  sem_filter_time:                        0.
% 2.40/0.99  monotx_time:                            0.001
% 2.40/0.99  subtype_inf_time:                       0.
% 2.40/0.99  
% 2.40/0.99  ------ Problem properties
% 2.40/0.99  
% 2.40/0.99  clauses:                                22
% 2.40/0.99  conjectures:                            5
% 2.40/0.99  epr:                                    4
% 2.40/0.99  horn:                                   17
% 2.40/0.99  ground:                                 11
% 2.40/0.99  unary:                                  6
% 2.40/0.99  binary:                                 7
% 2.40/0.99  lits:                                   57
% 2.40/0.99  lits_eq:                                23
% 2.40/0.99  fd_pure:                                0
% 2.40/0.99  fd_pseudo:                              0
% 2.40/0.99  fd_cond:                                0
% 2.40/0.99  fd_pseudo_cond:                         3
% 2.40/0.99  ac_symbols:                             0
% 2.40/0.99  
% 2.40/0.99  ------ Propositional Solver
% 2.40/0.99  
% 2.40/0.99  prop_solver_calls:                      26
% 2.40/0.99  prop_fast_solver_calls:                 826
% 2.40/0.99  smt_solver_calls:                       0
% 2.40/0.99  smt_fast_solver_calls:                  0
% 2.40/0.99  prop_num_of_clauses:                    1312
% 2.40/0.99  prop_preprocess_simplified:             4307
% 2.40/0.99  prop_fo_subsumed:                       21
% 2.40/0.99  prop_solver_time:                       0.
% 2.40/0.99  smt_solver_time:                        0.
% 2.40/0.99  smt_fast_solver_time:                   0.
% 2.40/0.99  prop_fast_solver_time:                  0.
% 2.40/0.99  prop_unsat_core_time:                   0.
% 2.40/0.99  
% 2.40/0.99  ------ QBF
% 2.40/0.99  
% 2.40/0.99  qbf_q_res:                              0
% 2.40/0.99  qbf_num_tautologies:                    0
% 2.40/0.99  qbf_prep_cycles:                        0
% 2.40/0.99  
% 2.40/0.99  ------ BMC1
% 2.40/0.99  
% 2.40/0.99  bmc1_current_bound:                     -1
% 2.40/0.99  bmc1_last_solved_bound:                 -1
% 2.40/0.99  bmc1_unsat_core_size:                   -1
% 2.40/0.99  bmc1_unsat_core_parents_size:           -1
% 2.40/0.99  bmc1_merge_next_fun:                    0
% 2.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation
% 2.40/0.99  
% 2.40/0.99  inst_num_of_clauses:                    420
% 2.40/0.99  inst_num_in_passive:                    61
% 2.40/0.99  inst_num_in_active:                     216
% 2.40/0.99  inst_num_in_unprocessed:                143
% 2.40/0.99  inst_num_of_loops:                      280
% 2.40/0.99  inst_num_of_learning_restarts:          0
% 2.40/0.99  inst_num_moves_active_passive:          61
% 2.40/0.99  inst_lit_activity:                      0
% 2.40/0.99  inst_lit_activity_moves:                0
% 2.40/0.99  inst_num_tautologies:                   0
% 2.40/0.99  inst_num_prop_implied:                  0
% 2.40/0.99  inst_num_existing_simplified:           0
% 2.40/0.99  inst_num_eq_res_simplified:             0
% 2.40/0.99  inst_num_child_elim:                    0
% 2.40/0.99  inst_num_of_dismatching_blockings:      202
% 2.40/0.99  inst_num_of_non_proper_insts:           497
% 2.40/0.99  inst_num_of_duplicates:                 0
% 2.40/0.99  inst_inst_num_from_inst_to_res:         0
% 2.40/0.99  inst_dismatching_checking_time:         0.
% 2.40/0.99  
% 2.40/0.99  ------ Resolution
% 2.40/0.99  
% 2.40/0.99  res_num_of_clauses:                     0
% 2.40/0.99  res_num_in_passive:                     0
% 2.40/0.99  res_num_in_active:                      0
% 2.40/0.99  res_num_of_loops:                       120
% 2.40/0.99  res_forward_subset_subsumed:            34
% 2.40/0.99  res_backward_subset_subsumed:           0
% 2.40/0.99  res_forward_subsumed:                   0
% 2.40/0.99  res_backward_subsumed:                  0
% 2.40/0.99  res_forward_subsumption_resolution:     0
% 2.40/0.99  res_backward_subsumption_resolution:    0
% 2.40/0.99  res_clause_to_clause_subsumption:       80
% 2.40/0.99  res_orphan_elimination:                 0
% 2.40/0.99  res_tautology_del:                      57
% 2.40/0.99  res_num_eq_res_simplified:              0
% 2.40/0.99  res_num_sel_changes:                    0
% 2.40/0.99  res_moves_from_active_to_pass:          0
% 2.40/0.99  
% 2.40/0.99  ------ Superposition
% 2.40/0.99  
% 2.40/0.99  sup_time_total:                         0.
% 2.40/0.99  sup_time_generating:                    0.
% 2.40/0.99  sup_time_sim_full:                      0.
% 2.40/0.99  sup_time_sim_immed:                     0.
% 2.40/0.99  
% 2.40/0.99  sup_num_of_clauses:                     58
% 2.40/0.99  sup_num_in_active:                      49
% 2.40/0.99  sup_num_in_passive:                     9
% 2.40/0.99  sup_num_of_loops:                       55
% 2.40/0.99  sup_fw_superposition:                   28
% 2.40/0.99  sup_bw_superposition:                   20
% 2.40/0.99  sup_immediate_simplified:               6
% 2.40/0.99  sup_given_eliminated:                   1
% 2.40/0.99  comparisons_done:                       0
% 2.40/0.99  comparisons_avoided:                    0
% 2.40/0.99  
% 2.40/0.99  ------ Simplifications
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  sim_fw_subset_subsumed:                 1
% 2.40/0.99  sim_bw_subset_subsumed:                 2
% 2.40/0.99  sim_fw_subsumed:                        2
% 2.40/0.99  sim_bw_subsumed:                        0
% 2.40/0.99  sim_fw_subsumption_res:                 0
% 2.40/0.99  sim_bw_subsumption_res:                 0
% 2.40/0.99  sim_tautology_del:                      0
% 2.40/0.99  sim_eq_tautology_del:                   5
% 2.40/0.99  sim_eq_res_simp:                        1
% 2.40/0.99  sim_fw_demodulated:                     0
% 2.40/0.99  sim_bw_demodulated:                     6
% 2.40/0.99  sim_light_normalised:                   7
% 2.40/0.99  sim_joinable_taut:                      0
% 2.40/0.99  sim_joinable_simp:                      0
% 2.40/0.99  sim_ac_normalised:                      0
% 2.40/0.99  sim_smt_subsumption:                    0
% 2.40/0.99  
%------------------------------------------------------------------------------
