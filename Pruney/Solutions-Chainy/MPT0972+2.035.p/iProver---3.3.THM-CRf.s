%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:15 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  154 (2962 expanded)
%              Number of clauses        :   93 ( 888 expanded)
%              Number of leaves         :   18 ( 753 expanded)
%              Depth                    :   27
%              Number of atoms          :  513 (19475 expanded)
%              Number of equality atoms :  261 (4531 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ! [X4] :
        ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
        | ~ r2_hidden(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f40,f39])).

fof(f67,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_938,plain,
    ( X0 = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_925,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_2139,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_925])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_399,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_23])).

cnf(c_929,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_931,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1617,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_929,c_931])).

cnf(c_1772,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_399,c_1617])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_408,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_410,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_26])).

cnf(c_927,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1618,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_927,c_931])).

cnf(c_1805,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_410,c_1618])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_933,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1938,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_933])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1125,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1126,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_3004,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1938,c_32,c_34,c_1126])).

cnf(c_3005,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3004])).

cnf(c_3017,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3005])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1129,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_23])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_576,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_1535,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_575,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1707,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_3234,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_29,c_31,c_23,c_1129,c_1332,c_1535,c_1707])).

cnf(c_3240,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3234])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_930,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3245,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3240,c_930])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_934,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3292,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_934])).

cnf(c_3293,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3292])).

cnf(c_3295,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_28,c_26,c_25,c_23,c_1125,c_1128,c_1332,c_1535,c_1707,c_3293])).

cnf(c_3299,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1772,c_3295])).

cnf(c_3491,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3299,c_1805])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_935,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1915,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_935])).

cnf(c_3500,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3491,c_1915])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3561,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3500,c_4])).

cnf(c_292,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_937,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2178,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_937])).

cnf(c_3498,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3491,c_2178])).

cnf(c_3571,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3498,c_4])).

cnf(c_3774,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3561,c_292,c_3571])).

cnf(c_3785,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2139,c_3774])).

cnf(c_1914,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_935])).

cnf(c_3501,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3491,c_1914])).

cnf(c_3556,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3501,c_4])).

cnf(c_2177,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_937])).

cnf(c_3499,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3491,c_2177])).

cnf(c_3566,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3499,c_4])).

cnf(c_3755,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3556,c_292,c_3566])).

cnf(c_3766,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2139,c_3755])).

cnf(c_1270,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_1538,plain,
    ( sK5 != X0
    | sK5 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1545,plain,
    ( sK5 = sK4
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3785,c_3766,c_1707,c_1545,c_1535,c_1332,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:15:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.62/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.00  
% 2.62/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/1.00  
% 2.62/1.00  ------  iProver source info
% 2.62/1.00  
% 2.62/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.62/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/1.00  git: non_committed_changes: false
% 2.62/1.00  git: last_make_outside_of_git: false
% 2.62/1.00  
% 2.62/1.00  ------ 
% 2.62/1.00  
% 2.62/1.00  ------ Input Options
% 2.62/1.00  
% 2.62/1.00  --out_options                           all
% 2.62/1.00  --tptp_safe_out                         true
% 2.62/1.00  --problem_path                          ""
% 2.62/1.00  --include_path                          ""
% 2.62/1.00  --clausifier                            res/vclausify_rel
% 2.62/1.00  --clausifier_options                    --mode clausify
% 2.62/1.00  --stdin                                 false
% 2.62/1.00  --stats_out                             all
% 2.62/1.00  
% 2.62/1.00  ------ General Options
% 2.62/1.00  
% 2.62/1.00  --fof                                   false
% 2.62/1.00  --time_out_real                         305.
% 2.62/1.00  --time_out_virtual                      -1.
% 2.62/1.00  --symbol_type_check                     false
% 2.62/1.00  --clausify_out                          false
% 2.62/1.00  --sig_cnt_out                           false
% 2.62/1.00  --trig_cnt_out                          false
% 2.62/1.00  --trig_cnt_out_tolerance                1.
% 2.62/1.00  --trig_cnt_out_sk_spl                   false
% 2.62/1.00  --abstr_cl_out                          false
% 2.62/1.00  
% 2.62/1.00  ------ Global Options
% 2.62/1.00  
% 2.62/1.00  --schedule                              default
% 2.62/1.00  --add_important_lit                     false
% 2.62/1.00  --prop_solver_per_cl                    1000
% 2.62/1.00  --min_unsat_core                        false
% 2.62/1.00  --soft_assumptions                      false
% 2.62/1.00  --soft_lemma_size                       3
% 2.62/1.00  --prop_impl_unit_size                   0
% 2.62/1.00  --prop_impl_unit                        []
% 2.62/1.00  --share_sel_clauses                     true
% 2.62/1.00  --reset_solvers                         false
% 2.62/1.00  --bc_imp_inh                            [conj_cone]
% 2.62/1.00  --conj_cone_tolerance                   3.
% 2.62/1.00  --extra_neg_conj                        none
% 2.62/1.00  --large_theory_mode                     true
% 2.62/1.00  --prolific_symb_bound                   200
% 2.62/1.00  --lt_threshold                          2000
% 2.62/1.00  --clause_weak_htbl                      true
% 2.62/1.00  --gc_record_bc_elim                     false
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing Options
% 2.62/1.00  
% 2.62/1.00  --preprocessing_flag                    true
% 2.62/1.00  --time_out_prep_mult                    0.1
% 2.62/1.00  --splitting_mode                        input
% 2.62/1.00  --splitting_grd                         true
% 2.62/1.00  --splitting_cvd                         false
% 2.62/1.00  --splitting_cvd_svl                     false
% 2.62/1.00  --splitting_nvd                         32
% 2.62/1.00  --sub_typing                            true
% 2.62/1.00  --prep_gs_sim                           true
% 2.62/1.00  --prep_unflatten                        true
% 2.62/1.00  --prep_res_sim                          true
% 2.62/1.00  --prep_upred                            true
% 2.62/1.00  --prep_sem_filter                       exhaustive
% 2.62/1.00  --prep_sem_filter_out                   false
% 2.62/1.00  --pred_elim                             true
% 2.62/1.00  --res_sim_input                         true
% 2.62/1.00  --eq_ax_congr_red                       true
% 2.62/1.00  --pure_diseq_elim                       true
% 2.62/1.00  --brand_transform                       false
% 2.62/1.00  --non_eq_to_eq                          false
% 2.62/1.00  --prep_def_merge                        true
% 2.62/1.00  --prep_def_merge_prop_impl              false
% 2.62/1.00  --prep_def_merge_mbd                    true
% 2.62/1.00  --prep_def_merge_tr_red                 false
% 2.62/1.00  --prep_def_merge_tr_cl                  false
% 2.62/1.00  --smt_preprocessing                     true
% 2.62/1.00  --smt_ac_axioms                         fast
% 2.62/1.00  --preprocessed_out                      false
% 2.62/1.00  --preprocessed_stats                    false
% 2.62/1.00  
% 2.62/1.00  ------ Abstraction refinement Options
% 2.62/1.00  
% 2.62/1.00  --abstr_ref                             []
% 2.62/1.00  --abstr_ref_prep                        false
% 2.62/1.00  --abstr_ref_until_sat                   false
% 2.62/1.00  --abstr_ref_sig_restrict                funpre
% 2.62/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.00  --abstr_ref_under                       []
% 2.62/1.00  
% 2.62/1.00  ------ SAT Options
% 2.62/1.00  
% 2.62/1.00  --sat_mode                              false
% 2.62/1.00  --sat_fm_restart_options                ""
% 2.62/1.00  --sat_gr_def                            false
% 2.62/1.00  --sat_epr_types                         true
% 2.62/1.00  --sat_non_cyclic_types                  false
% 2.62/1.00  --sat_finite_models                     false
% 2.62/1.00  --sat_fm_lemmas                         false
% 2.62/1.00  --sat_fm_prep                           false
% 2.62/1.00  --sat_fm_uc_incr                        true
% 2.62/1.00  --sat_out_model                         small
% 2.62/1.00  --sat_out_clauses                       false
% 2.62/1.00  
% 2.62/1.00  ------ QBF Options
% 2.62/1.00  
% 2.62/1.00  --qbf_mode                              false
% 2.62/1.00  --qbf_elim_univ                         false
% 2.62/1.00  --qbf_dom_inst                          none
% 2.62/1.00  --qbf_dom_pre_inst                      false
% 2.62/1.00  --qbf_sk_in                             false
% 2.62/1.00  --qbf_pred_elim                         true
% 2.62/1.00  --qbf_split                             512
% 2.62/1.00  
% 2.62/1.00  ------ BMC1 Options
% 2.62/1.00  
% 2.62/1.00  --bmc1_incremental                      false
% 2.62/1.00  --bmc1_axioms                           reachable_all
% 2.62/1.00  --bmc1_min_bound                        0
% 2.62/1.00  --bmc1_max_bound                        -1
% 2.62/1.00  --bmc1_max_bound_default                -1
% 2.62/1.00  --bmc1_symbol_reachability              true
% 2.62/1.00  --bmc1_property_lemmas                  false
% 2.62/1.00  --bmc1_k_induction                      false
% 2.62/1.00  --bmc1_non_equiv_states                 false
% 2.62/1.00  --bmc1_deadlock                         false
% 2.62/1.00  --bmc1_ucm                              false
% 2.62/1.00  --bmc1_add_unsat_core                   none
% 2.62/1.00  --bmc1_unsat_core_children              false
% 2.62/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.00  --bmc1_out_stat                         full
% 2.62/1.00  --bmc1_ground_init                      false
% 2.62/1.00  --bmc1_pre_inst_next_state              false
% 2.62/1.00  --bmc1_pre_inst_state                   false
% 2.62/1.00  --bmc1_pre_inst_reach_state             false
% 2.62/1.00  --bmc1_out_unsat_core                   false
% 2.62/1.00  --bmc1_aig_witness_out                  false
% 2.62/1.00  --bmc1_verbose                          false
% 2.62/1.00  --bmc1_dump_clauses_tptp                false
% 2.62/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.00  --bmc1_dump_file                        -
% 2.62/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.00  --bmc1_ucm_extend_mode                  1
% 2.62/1.00  --bmc1_ucm_init_mode                    2
% 2.62/1.00  --bmc1_ucm_cone_mode                    none
% 2.62/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.00  --bmc1_ucm_relax_model                  4
% 2.62/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.00  --bmc1_ucm_layered_model                none
% 2.62/1.00  --bmc1_ucm_max_lemma_size               10
% 2.62/1.00  
% 2.62/1.00  ------ AIG Options
% 2.62/1.00  
% 2.62/1.00  --aig_mode                              false
% 2.62/1.00  
% 2.62/1.00  ------ Instantiation Options
% 2.62/1.00  
% 2.62/1.00  --instantiation_flag                    true
% 2.62/1.00  --inst_sos_flag                         false
% 2.62/1.00  --inst_sos_phase                        true
% 2.62/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.00  --inst_lit_sel_side                     num_symb
% 2.62/1.00  --inst_solver_per_active                1400
% 2.62/1.00  --inst_solver_calls_frac                1.
% 2.62/1.00  --inst_passive_queue_type               priority_queues
% 2.62/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.00  --inst_passive_queues_freq              [25;2]
% 2.62/1.00  --inst_dismatching                      true
% 2.62/1.00  --inst_eager_unprocessed_to_passive     true
% 2.62/1.00  --inst_prop_sim_given                   true
% 2.62/1.00  --inst_prop_sim_new                     false
% 2.62/1.00  --inst_subs_new                         false
% 2.62/1.00  --inst_eq_res_simp                      false
% 2.62/1.00  --inst_subs_given                       false
% 2.62/1.00  --inst_orphan_elimination               true
% 2.62/1.00  --inst_learning_loop_flag               true
% 2.62/1.00  --inst_learning_start                   3000
% 2.62/1.00  --inst_learning_factor                  2
% 2.62/1.00  --inst_start_prop_sim_after_learn       3
% 2.62/1.00  --inst_sel_renew                        solver
% 2.62/1.00  --inst_lit_activity_flag                true
% 2.62/1.00  --inst_restr_to_given                   false
% 2.62/1.00  --inst_activity_threshold               500
% 2.62/1.00  --inst_out_proof                        true
% 2.62/1.00  
% 2.62/1.00  ------ Resolution Options
% 2.62/1.00  
% 2.62/1.00  --resolution_flag                       true
% 2.62/1.00  --res_lit_sel                           adaptive
% 2.62/1.00  --res_lit_sel_side                      none
% 2.62/1.00  --res_ordering                          kbo
% 2.62/1.00  --res_to_prop_solver                    active
% 2.62/1.00  --res_prop_simpl_new                    false
% 2.62/1.00  --res_prop_simpl_given                  true
% 2.62/1.00  --res_passive_queue_type                priority_queues
% 2.62/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.00  --res_passive_queues_freq               [15;5]
% 2.62/1.00  --res_forward_subs                      full
% 2.62/1.00  --res_backward_subs                     full
% 2.62/1.00  --res_forward_subs_resolution           true
% 2.62/1.00  --res_backward_subs_resolution          true
% 2.62/1.00  --res_orphan_elimination                true
% 2.62/1.00  --res_time_limit                        2.
% 2.62/1.00  --res_out_proof                         true
% 2.62/1.00  
% 2.62/1.00  ------ Superposition Options
% 2.62/1.00  
% 2.62/1.00  --superposition_flag                    true
% 2.62/1.00  --sup_passive_queue_type                priority_queues
% 2.62/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.00  --demod_completeness_check              fast
% 2.62/1.00  --demod_use_ground                      true
% 2.62/1.00  --sup_to_prop_solver                    passive
% 2.62/1.00  --sup_prop_simpl_new                    true
% 2.62/1.00  --sup_prop_simpl_given                  true
% 2.62/1.00  --sup_fun_splitting                     false
% 2.62/1.00  --sup_smt_interval                      50000
% 2.62/1.00  
% 2.62/1.00  ------ Superposition Simplification Setup
% 2.62/1.00  
% 2.62/1.00  --sup_indices_passive                   []
% 2.62/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_full_bw                           [BwDemod]
% 2.62/1.00  --sup_immed_triv                        [TrivRules]
% 2.62/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_immed_bw_main                     []
% 2.62/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.00  
% 2.62/1.00  ------ Combination Options
% 2.62/1.00  
% 2.62/1.00  --comb_res_mult                         3
% 2.62/1.00  --comb_sup_mult                         2
% 2.62/1.00  --comb_inst_mult                        10
% 2.62/1.00  
% 2.62/1.00  ------ Debug Options
% 2.62/1.00  
% 2.62/1.00  --dbg_backtrace                         false
% 2.62/1.00  --dbg_dump_prop_clauses                 false
% 2.62/1.00  --dbg_dump_prop_clauses_file            -
% 2.62/1.00  --dbg_out_stat                          false
% 2.62/1.00  ------ Parsing...
% 2.62/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/1.00  ------ Proving...
% 2.62/1.00  ------ Problem Properties 
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  clauses                                 25
% 2.62/1.00  conjectures                             5
% 2.62/1.00  EPR                                     3
% 2.62/1.00  Horn                                    18
% 2.62/1.00  unary                                   8
% 2.62/1.00  binary                                  6
% 2.62/1.00  lits                                    63
% 2.62/1.00  lits eq                                 29
% 2.62/1.00  fd_pure                                 0
% 2.62/1.00  fd_pseudo                               0
% 2.62/1.00  fd_cond                                 1
% 2.62/1.00  fd_pseudo_cond                          4
% 2.62/1.00  AC symbols                              0
% 2.62/1.00  
% 2.62/1.00  ------ Schedule dynamic 5 is on 
% 2.62/1.00  
% 2.62/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  ------ 
% 2.62/1.00  Current options:
% 2.62/1.00  ------ 
% 2.62/1.00  
% 2.62/1.00  ------ Input Options
% 2.62/1.00  
% 2.62/1.00  --out_options                           all
% 2.62/1.00  --tptp_safe_out                         true
% 2.62/1.00  --problem_path                          ""
% 2.62/1.00  --include_path                          ""
% 2.62/1.00  --clausifier                            res/vclausify_rel
% 2.62/1.00  --clausifier_options                    --mode clausify
% 2.62/1.00  --stdin                                 false
% 2.62/1.00  --stats_out                             all
% 2.62/1.00  
% 2.62/1.00  ------ General Options
% 2.62/1.00  
% 2.62/1.00  --fof                                   false
% 2.62/1.00  --time_out_real                         305.
% 2.62/1.00  --time_out_virtual                      -1.
% 2.62/1.00  --symbol_type_check                     false
% 2.62/1.00  --clausify_out                          false
% 2.62/1.00  --sig_cnt_out                           false
% 2.62/1.00  --trig_cnt_out                          false
% 2.62/1.00  --trig_cnt_out_tolerance                1.
% 2.62/1.00  --trig_cnt_out_sk_spl                   false
% 2.62/1.00  --abstr_cl_out                          false
% 2.62/1.00  
% 2.62/1.00  ------ Global Options
% 2.62/1.00  
% 2.62/1.00  --schedule                              default
% 2.62/1.00  --add_important_lit                     false
% 2.62/1.00  --prop_solver_per_cl                    1000
% 2.62/1.00  --min_unsat_core                        false
% 2.62/1.00  --soft_assumptions                      false
% 2.62/1.00  --soft_lemma_size                       3
% 2.62/1.00  --prop_impl_unit_size                   0
% 2.62/1.00  --prop_impl_unit                        []
% 2.62/1.00  --share_sel_clauses                     true
% 2.62/1.00  --reset_solvers                         false
% 2.62/1.00  --bc_imp_inh                            [conj_cone]
% 2.62/1.00  --conj_cone_tolerance                   3.
% 2.62/1.00  --extra_neg_conj                        none
% 2.62/1.00  --large_theory_mode                     true
% 2.62/1.00  --prolific_symb_bound                   200
% 2.62/1.00  --lt_threshold                          2000
% 2.62/1.00  --clause_weak_htbl                      true
% 2.62/1.00  --gc_record_bc_elim                     false
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing Options
% 2.62/1.00  
% 2.62/1.00  --preprocessing_flag                    true
% 2.62/1.00  --time_out_prep_mult                    0.1
% 2.62/1.00  --splitting_mode                        input
% 2.62/1.00  --splitting_grd                         true
% 2.62/1.00  --splitting_cvd                         false
% 2.62/1.00  --splitting_cvd_svl                     false
% 2.62/1.00  --splitting_nvd                         32
% 2.62/1.00  --sub_typing                            true
% 2.62/1.00  --prep_gs_sim                           true
% 2.62/1.00  --prep_unflatten                        true
% 2.62/1.00  --prep_res_sim                          true
% 2.62/1.00  --prep_upred                            true
% 2.62/1.00  --prep_sem_filter                       exhaustive
% 2.62/1.00  --prep_sem_filter_out                   false
% 2.62/1.00  --pred_elim                             true
% 2.62/1.00  --res_sim_input                         true
% 2.62/1.00  --eq_ax_congr_red                       true
% 2.62/1.00  --pure_diseq_elim                       true
% 2.62/1.00  --brand_transform                       false
% 2.62/1.00  --non_eq_to_eq                          false
% 2.62/1.00  --prep_def_merge                        true
% 2.62/1.00  --prep_def_merge_prop_impl              false
% 2.62/1.00  --prep_def_merge_mbd                    true
% 2.62/1.00  --prep_def_merge_tr_red                 false
% 2.62/1.00  --prep_def_merge_tr_cl                  false
% 2.62/1.00  --smt_preprocessing                     true
% 2.62/1.00  --smt_ac_axioms                         fast
% 2.62/1.00  --preprocessed_out                      false
% 2.62/1.00  --preprocessed_stats                    false
% 2.62/1.00  
% 2.62/1.00  ------ Abstraction refinement Options
% 2.62/1.00  
% 2.62/1.00  --abstr_ref                             []
% 2.62/1.00  --abstr_ref_prep                        false
% 2.62/1.00  --abstr_ref_until_sat                   false
% 2.62/1.00  --abstr_ref_sig_restrict                funpre
% 2.62/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.00  --abstr_ref_under                       []
% 2.62/1.00  
% 2.62/1.00  ------ SAT Options
% 2.62/1.00  
% 2.62/1.00  --sat_mode                              false
% 2.62/1.00  --sat_fm_restart_options                ""
% 2.62/1.00  --sat_gr_def                            false
% 2.62/1.00  --sat_epr_types                         true
% 2.62/1.00  --sat_non_cyclic_types                  false
% 2.62/1.00  --sat_finite_models                     false
% 2.62/1.00  --sat_fm_lemmas                         false
% 2.62/1.00  --sat_fm_prep                           false
% 2.62/1.00  --sat_fm_uc_incr                        true
% 2.62/1.00  --sat_out_model                         small
% 2.62/1.00  --sat_out_clauses                       false
% 2.62/1.00  
% 2.62/1.00  ------ QBF Options
% 2.62/1.00  
% 2.62/1.00  --qbf_mode                              false
% 2.62/1.00  --qbf_elim_univ                         false
% 2.62/1.00  --qbf_dom_inst                          none
% 2.62/1.00  --qbf_dom_pre_inst                      false
% 2.62/1.00  --qbf_sk_in                             false
% 2.62/1.00  --qbf_pred_elim                         true
% 2.62/1.00  --qbf_split                             512
% 2.62/1.00  
% 2.62/1.00  ------ BMC1 Options
% 2.62/1.00  
% 2.62/1.00  --bmc1_incremental                      false
% 2.62/1.00  --bmc1_axioms                           reachable_all
% 2.62/1.00  --bmc1_min_bound                        0
% 2.62/1.00  --bmc1_max_bound                        -1
% 2.62/1.00  --bmc1_max_bound_default                -1
% 2.62/1.00  --bmc1_symbol_reachability              true
% 2.62/1.00  --bmc1_property_lemmas                  false
% 2.62/1.00  --bmc1_k_induction                      false
% 2.62/1.00  --bmc1_non_equiv_states                 false
% 2.62/1.00  --bmc1_deadlock                         false
% 2.62/1.00  --bmc1_ucm                              false
% 2.62/1.00  --bmc1_add_unsat_core                   none
% 2.62/1.00  --bmc1_unsat_core_children              false
% 2.62/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.00  --bmc1_out_stat                         full
% 2.62/1.00  --bmc1_ground_init                      false
% 2.62/1.00  --bmc1_pre_inst_next_state              false
% 2.62/1.00  --bmc1_pre_inst_state                   false
% 2.62/1.00  --bmc1_pre_inst_reach_state             false
% 2.62/1.00  --bmc1_out_unsat_core                   false
% 2.62/1.00  --bmc1_aig_witness_out                  false
% 2.62/1.00  --bmc1_verbose                          false
% 2.62/1.00  --bmc1_dump_clauses_tptp                false
% 2.62/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.00  --bmc1_dump_file                        -
% 2.62/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.00  --bmc1_ucm_extend_mode                  1
% 2.62/1.00  --bmc1_ucm_init_mode                    2
% 2.62/1.00  --bmc1_ucm_cone_mode                    none
% 2.62/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.00  --bmc1_ucm_relax_model                  4
% 2.62/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.00  --bmc1_ucm_layered_model                none
% 2.62/1.00  --bmc1_ucm_max_lemma_size               10
% 2.62/1.00  
% 2.62/1.00  ------ AIG Options
% 2.62/1.00  
% 2.62/1.00  --aig_mode                              false
% 2.62/1.00  
% 2.62/1.00  ------ Instantiation Options
% 2.62/1.00  
% 2.62/1.00  --instantiation_flag                    true
% 2.62/1.00  --inst_sos_flag                         false
% 2.62/1.00  --inst_sos_phase                        true
% 2.62/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.00  --inst_lit_sel_side                     none
% 2.62/1.00  --inst_solver_per_active                1400
% 2.62/1.00  --inst_solver_calls_frac                1.
% 2.62/1.00  --inst_passive_queue_type               priority_queues
% 2.62/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.00  --inst_passive_queues_freq              [25;2]
% 2.62/1.00  --inst_dismatching                      true
% 2.62/1.00  --inst_eager_unprocessed_to_passive     true
% 2.62/1.00  --inst_prop_sim_given                   true
% 2.62/1.00  --inst_prop_sim_new                     false
% 2.62/1.00  --inst_subs_new                         false
% 2.62/1.00  --inst_eq_res_simp                      false
% 2.62/1.00  --inst_subs_given                       false
% 2.62/1.00  --inst_orphan_elimination               true
% 2.62/1.00  --inst_learning_loop_flag               true
% 2.62/1.00  --inst_learning_start                   3000
% 2.62/1.00  --inst_learning_factor                  2
% 2.62/1.00  --inst_start_prop_sim_after_learn       3
% 2.62/1.00  --inst_sel_renew                        solver
% 2.62/1.00  --inst_lit_activity_flag                true
% 2.62/1.00  --inst_restr_to_given                   false
% 2.62/1.00  --inst_activity_threshold               500
% 2.62/1.00  --inst_out_proof                        true
% 2.62/1.00  
% 2.62/1.00  ------ Resolution Options
% 2.62/1.00  
% 2.62/1.00  --resolution_flag                       false
% 2.62/1.00  --res_lit_sel                           adaptive
% 2.62/1.00  --res_lit_sel_side                      none
% 2.62/1.00  --res_ordering                          kbo
% 2.62/1.00  --res_to_prop_solver                    active
% 2.62/1.00  --res_prop_simpl_new                    false
% 2.62/1.00  --res_prop_simpl_given                  true
% 2.62/1.00  --res_passive_queue_type                priority_queues
% 2.62/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.00  --res_passive_queues_freq               [15;5]
% 2.62/1.00  --res_forward_subs                      full
% 2.62/1.00  --res_backward_subs                     full
% 2.62/1.00  --res_forward_subs_resolution           true
% 2.62/1.00  --res_backward_subs_resolution          true
% 2.62/1.00  --res_orphan_elimination                true
% 2.62/1.00  --res_time_limit                        2.
% 2.62/1.00  --res_out_proof                         true
% 2.62/1.00  
% 2.62/1.00  ------ Superposition Options
% 2.62/1.00  
% 2.62/1.00  --superposition_flag                    true
% 2.62/1.00  --sup_passive_queue_type                priority_queues
% 2.62/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.00  --demod_completeness_check              fast
% 2.62/1.00  --demod_use_ground                      true
% 2.62/1.00  --sup_to_prop_solver                    passive
% 2.62/1.00  --sup_prop_simpl_new                    true
% 2.62/1.00  --sup_prop_simpl_given                  true
% 2.62/1.00  --sup_fun_splitting                     false
% 2.62/1.00  --sup_smt_interval                      50000
% 2.62/1.00  
% 2.62/1.00  ------ Superposition Simplification Setup
% 2.62/1.00  
% 2.62/1.00  --sup_indices_passive                   []
% 2.62/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_full_bw                           [BwDemod]
% 2.62/1.00  --sup_immed_triv                        [TrivRules]
% 2.62/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_immed_bw_main                     []
% 2.62/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.00  
% 2.62/1.00  ------ Combination Options
% 2.62/1.00  
% 2.62/1.00  --comb_res_mult                         3
% 2.62/1.00  --comb_sup_mult                         2
% 2.62/1.00  --comb_inst_mult                        10
% 2.62/1.00  
% 2.62/1.00  ------ Debug Options
% 2.62/1.00  
% 2.62/1.00  --dbg_backtrace                         false
% 2.62/1.00  --dbg_dump_prop_clauses                 false
% 2.62/1.00  --dbg_dump_prop_clauses_file            -
% 2.62/1.00  --dbg_out_stat                          false
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  ------ Proving...
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  % SZS status Theorem for theBenchmark.p
% 2.62/1.00  
% 2.62/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/1.00  
% 2.62/1.00  fof(f3,axiom,(
% 2.62/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f17,plain,(
% 2.62/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.62/1.00    inference(ennf_transformation,[],[f3])).
% 2.62/1.00  
% 2.62/1.00  fof(f31,plain,(
% 2.62/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.62/1.00    inference(nnf_transformation,[],[f17])).
% 2.62/1.00  
% 2.62/1.00  fof(f32,plain,(
% 2.62/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.62/1.00    introduced(choice_axiom,[])).
% 2.62/1.00  
% 2.62/1.00  fof(f33,plain,(
% 2.62/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.62/1.00  
% 2.62/1.00  fof(f44,plain,(
% 2.62/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f33])).
% 2.62/1.00  
% 2.62/1.00  fof(f1,axiom,(
% 2.62/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f15,plain,(
% 2.62/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.62/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.62/1.00  
% 2.62/1.00  fof(f16,plain,(
% 2.62/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.62/1.00    inference(ennf_transformation,[],[f15])).
% 2.62/1.00  
% 2.62/1.00  fof(f42,plain,(
% 2.62/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f16])).
% 2.62/1.00  
% 2.62/1.00  fof(f2,axiom,(
% 2.62/1.00    v1_xboole_0(k1_xboole_0)),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f43,plain,(
% 2.62/1.00    v1_xboole_0(k1_xboole_0)),
% 2.62/1.00    inference(cnf_transformation,[],[f2])).
% 2.62/1.00  
% 2.62/1.00  fof(f12,axiom,(
% 2.62/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f27,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(ennf_transformation,[],[f12])).
% 2.62/1.00  
% 2.62/1.00  fof(f28,plain,(
% 2.62/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(flattening,[],[f27])).
% 2.62/1.00  
% 2.62/1.00  fof(f38,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(nnf_transformation,[],[f28])).
% 2.62/1.00  
% 2.62/1.00  fof(f57,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.00    inference(cnf_transformation,[],[f38])).
% 2.62/1.00  
% 2.62/1.00  fof(f13,conjecture,(
% 2.62/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f14,negated_conjecture,(
% 2.62/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.62/1.00    inference(negated_conjecture,[],[f13])).
% 2.62/1.00  
% 2.62/1.00  fof(f29,plain,(
% 2.62/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.62/1.00    inference(ennf_transformation,[],[f14])).
% 2.62/1.00  
% 2.62/1.00  fof(f30,plain,(
% 2.62/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.62/1.00    inference(flattening,[],[f29])).
% 2.62/1.00  
% 2.62/1.00  fof(f40,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.62/1.00    introduced(choice_axiom,[])).
% 2.62/1.00  
% 2.62/1.00  fof(f39,plain,(
% 2.62/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.62/1.00    introduced(choice_axiom,[])).
% 2.62/1.00  
% 2.62/1.00  fof(f41,plain,(
% 2.62/1.00    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f40,f39])).
% 2.62/1.00  
% 2.62/1.00  fof(f67,plain,(
% 2.62/1.00    v1_funct_2(sK5,sK2,sK3)),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f68,plain,(
% 2.62/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f10,axiom,(
% 2.62/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f24,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(ennf_transformation,[],[f10])).
% 2.62/1.00  
% 2.62/1.00  fof(f55,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.00    inference(cnf_transformation,[],[f24])).
% 2.62/1.00  
% 2.62/1.00  fof(f64,plain,(
% 2.62/1.00    v1_funct_2(sK4,sK2,sK3)),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f65,plain,(
% 2.62/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f8,axiom,(
% 2.62/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f21,plain,(
% 2.62/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/1.00    inference(ennf_transformation,[],[f8])).
% 2.62/1.00  
% 2.62/1.00  fof(f22,plain,(
% 2.62/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/1.00    inference(flattening,[],[f21])).
% 2.62/1.00  
% 2.62/1.00  fof(f36,plain,(
% 2.62/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.62/1.00    introduced(choice_axiom,[])).
% 2.62/1.00  
% 2.62/1.00  fof(f37,plain,(
% 2.62/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f36])).
% 2.62/1.00  
% 2.62/1.00  fof(f52,plain,(
% 2.62/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f37])).
% 2.62/1.00  
% 2.62/1.00  fof(f66,plain,(
% 2.62/1.00    v1_funct_1(sK5)),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f9,axiom,(
% 2.62/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f23,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(ennf_transformation,[],[f9])).
% 2.62/1.00  
% 2.62/1.00  fof(f54,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.00    inference(cnf_transformation,[],[f23])).
% 2.62/1.00  
% 2.62/1.00  fof(f63,plain,(
% 2.62/1.00    v1_funct_1(sK4)),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f11,axiom,(
% 2.62/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f25,plain,(
% 2.62/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.62/1.00    inference(ennf_transformation,[],[f11])).
% 2.62/1.00  
% 2.62/1.00  fof(f26,plain,(
% 2.62/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.00    inference(flattening,[],[f25])).
% 2.62/1.00  
% 2.62/1.00  fof(f56,plain,(
% 2.62/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.00    inference(cnf_transformation,[],[f26])).
% 2.62/1.00  
% 2.62/1.00  fof(f70,plain,(
% 2.62/1.00    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f69,plain,(
% 2.62/1.00    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f41])).
% 2.62/1.00  
% 2.62/1.00  fof(f53,plain,(
% 2.62/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f37])).
% 2.62/1.00  
% 2.62/1.00  fof(f7,axiom,(
% 2.62/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f19,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.62/1.00    inference(ennf_transformation,[],[f7])).
% 2.62/1.00  
% 2.62/1.00  fof(f20,plain,(
% 2.62/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.62/1.00    inference(flattening,[],[f19])).
% 2.62/1.00  
% 2.62/1.00  fof(f51,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.62/1.00    inference(cnf_transformation,[],[f20])).
% 2.62/1.00  
% 2.62/1.00  fof(f4,axiom,(
% 2.62/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f34,plain,(
% 2.62/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.62/1.00    inference(nnf_transformation,[],[f4])).
% 2.62/1.00  
% 2.62/1.00  fof(f35,plain,(
% 2.62/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.62/1.00    inference(flattening,[],[f34])).
% 2.62/1.00  
% 2.62/1.00  fof(f48,plain,(
% 2.62/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.62/1.00    inference(cnf_transformation,[],[f35])).
% 2.62/1.00  
% 2.62/1.00  fof(f71,plain,(
% 2.62/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.62/1.00    inference(equality_resolution,[],[f48])).
% 2.62/1.00  
% 2.62/1.00  fof(f5,axiom,(
% 2.62/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/1.00  
% 2.62/1.00  fof(f18,plain,(
% 2.62/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.62/1.00    inference(ennf_transformation,[],[f5])).
% 2.62/1.00  
% 2.62/1.00  fof(f49,plain,(
% 2.62/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.62/1.00    inference(cnf_transformation,[],[f18])).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3,plain,
% 2.62/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X0 = X1 ),
% 2.62/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_938,plain,
% 2.62/1.00      ( X0 = X1
% 2.62/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.62/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_0,plain,
% 2.62/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.62/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1,plain,
% 2.62/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.62/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_290,plain,
% 2.62/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.62/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_291,plain,
% 2.62/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.62/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_925,plain,
% 2.62/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_2139,plain,
% 2.62/1.00      ( k1_xboole_0 = X0
% 2.62/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_938,c_925]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_20,plain,
% 2.62/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.62/1.00      | k1_xboole_0 = X2 ),
% 2.62/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_24,negated_conjecture,
% 2.62/1.00      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.62/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_396,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.62/1.00      | sK5 != X0
% 2.62/1.00      | sK3 != X2
% 2.62/1.00      | sK2 != X1
% 2.62/1.00      | k1_xboole_0 = X2 ),
% 2.62/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_397,plain,
% 2.62/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.62/1.00      | k1_xboole_0 = sK3 ),
% 2.62/1.00      inference(unflattening,[status(thm)],[c_396]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_23,negated_conjecture,
% 2.62/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.62/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_399,plain,
% 2.62/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_397,c_23]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_929,plain,
% 2.62/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_13,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.62/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_931,plain,
% 2.62/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.62/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1617,plain,
% 2.62/1.00      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_929,c_931]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1772,plain,
% 2.62/1.00      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_399,c_1617]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_27,negated_conjecture,
% 2.62/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.62/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_407,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.62/1.00      | sK4 != X0
% 2.62/1.00      | sK3 != X2
% 2.62/1.00      | sK2 != X1
% 2.62/1.00      | k1_xboole_0 = X2 ),
% 2.62/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_408,plain,
% 2.62/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.62/1.00      | k1_xboole_0 = sK3 ),
% 2.62/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_26,negated_conjecture,
% 2.62/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.62/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_410,plain,
% 2.62/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_408,c_26]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_927,plain,
% 2.62/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1618,plain,
% 2.62/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_927,c_931]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1805,plain,
% 2.62/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_410,c_1618]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_11,plain,
% 2.62/1.00      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.62/1.00      | ~ v1_relat_1(X1)
% 2.62/1.00      | ~ v1_relat_1(X0)
% 2.62/1.00      | ~ v1_funct_1(X1)
% 2.62/1.00      | ~ v1_funct_1(X0)
% 2.62/1.00      | X0 = X1
% 2.62/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.62/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_933,plain,
% 2.62/1.00      ( X0 = X1
% 2.62/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.62/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.62/1.00      | v1_relat_1(X0) != iProver_top
% 2.62/1.00      | v1_relat_1(X1) != iProver_top
% 2.62/1.00      | v1_funct_1(X1) != iProver_top
% 2.62/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1938,plain,
% 2.62/1.00      ( k1_relat_1(X0) != sK2
% 2.62/1.00      | sK5 = X0
% 2.62/1.00      | sK3 = k1_xboole_0
% 2.62/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.62/1.00      | v1_relat_1(X0) != iProver_top
% 2.62/1.00      | v1_relat_1(sK5) != iProver_top
% 2.62/1.00      | v1_funct_1(X0) != iProver_top
% 2.62/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_1772,c_933]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_25,negated_conjecture,
% 2.62/1.00      ( v1_funct_1(sK5) ),
% 2.62/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_32,plain,
% 2.62/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_34,plain,
% 2.62/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_12,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | v1_relat_1(X0) ),
% 2.62/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1125,plain,
% 2.62/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | v1_relat_1(sK5) ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1126,plain,
% 2.62/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.62/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3004,plain,
% 2.62/1.00      ( v1_funct_1(X0) != iProver_top
% 2.62/1.00      | k1_relat_1(X0) != sK2
% 2.62/1.00      | sK5 = X0
% 2.62/1.00      | sK3 = k1_xboole_0
% 2.62/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.62/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_1938,c_32,c_34,c_1126]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3005,plain,
% 2.62/1.00      ( k1_relat_1(X0) != sK2
% 2.62/1.00      | sK5 = X0
% 2.62/1.00      | sK3 = k1_xboole_0
% 2.62/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.62/1.00      | v1_relat_1(X0) != iProver_top
% 2.62/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.62/1.00      inference(renaming,[status(thm)],[c_3004]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3017,plain,
% 2.62/1.00      ( sK5 = sK4
% 2.62/1.00      | sK3 = k1_xboole_0
% 2.62/1.00      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.62/1.00      | v1_relat_1(sK4) != iProver_top
% 2.62/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_1805,c_3005]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_28,negated_conjecture,
% 2.62/1.00      ( v1_funct_1(sK4) ),
% 2.62/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_29,plain,
% 2.62/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_31,plain,
% 2.62/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1128,plain,
% 2.62/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | v1_relat_1(sK4) ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1129,plain,
% 2.62/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.62/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_14,plain,
% 2.62/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.62/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.62/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_21,negated_conjecture,
% 2.62/1.00      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.62/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_301,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.00      | sK5 != X0
% 2.62/1.00      | sK4 != X0
% 2.62/1.00      | sK3 != X2
% 2.62/1.00      | sK2 != X1 ),
% 2.62/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_302,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | sK4 != sK5 ),
% 2.62/1.00      inference(unflattening,[status(thm)],[c_301]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_306,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | sK4 != sK5 ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_302,c_23]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1332,plain,
% 2.62/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.62/1.00      | sK4 != sK5 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_576,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1145,plain,
% 2.62/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_576]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1535,plain,
% 2.62/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_575,plain,( X0 = X0 ),theory(equality) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1707,plain,
% 2.62/1.00      ( sK4 = sK4 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_575]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3234,plain,
% 2.62/1.00      ( sK3 = k1_xboole_0
% 2.62/1.00      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3017,c_29,c_31,c_23,c_1129,c_1332,c_1535,c_1707]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3240,plain,
% 2.62/1.00      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_1805,c_3234]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_22,negated_conjecture,
% 2.62/1.00      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.62/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_930,plain,
% 2.62/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.62/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3245,plain,
% 2.62/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.62/1.00      | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_3240,c_930]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_10,plain,
% 2.62/1.00      ( ~ v1_relat_1(X0)
% 2.62/1.00      | ~ v1_relat_1(X1)
% 2.62/1.00      | ~ v1_funct_1(X0)
% 2.62/1.00      | ~ v1_funct_1(X1)
% 2.62/1.00      | X1 = X0
% 2.62/1.00      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.62/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.62/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_934,plain,
% 2.62/1.00      ( X0 = X1
% 2.62/1.00      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.62/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.62/1.00      | v1_relat_1(X1) != iProver_top
% 2.62/1.00      | v1_relat_1(X0) != iProver_top
% 2.62/1.00      | v1_funct_1(X0) != iProver_top
% 2.62/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3292,plain,
% 2.62/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.62/1.00      | sK5 = sK4
% 2.62/1.00      | sK3 = k1_xboole_0
% 2.62/1.00      | v1_relat_1(sK5) != iProver_top
% 2.62/1.00      | v1_relat_1(sK4) != iProver_top
% 2.62/1.00      | v1_funct_1(sK5) != iProver_top
% 2.62/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_3245,c_934]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3293,plain,
% 2.62/1.00      ( ~ v1_relat_1(sK5)
% 2.62/1.00      | ~ v1_relat_1(sK4)
% 2.62/1.00      | ~ v1_funct_1(sK5)
% 2.62/1.00      | ~ v1_funct_1(sK4)
% 2.62/1.00      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.62/1.00      | sK5 = sK4
% 2.62/1.00      | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3292]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3295,plain,
% 2.62/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3292,c_28,c_26,c_25,c_23,c_1125,c_1128,c_1332,c_1535,
% 2.62/1.00                 c_1707,c_3293]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3299,plain,
% 2.62/1.00      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_1772,c_3295]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3491,plain,
% 2.62/1.00      ( sK3 = k1_xboole_0 ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3299,c_1805]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_9,plain,
% 2.62/1.00      ( m1_subset_1(X0,X1)
% 2.62/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.62/1.00      | ~ r2_hidden(X0,X2) ),
% 2.62/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_935,plain,
% 2.62/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.62/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.62/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1915,plain,
% 2.62/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_927,c_935]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3500,plain,
% 2.62/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3491,c_1915]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_4,plain,
% 2.62/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.62/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3561,plain,
% 2.62/1.00      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3500,c_4]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_292,plain,
% 2.62/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_7,plain,
% 2.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.62/1.00      | ~ r2_hidden(X2,X0)
% 2.62/1.00      | r2_hidden(X2,X1) ),
% 2.62/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_937,plain,
% 2.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.62/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.62/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.62/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_2178,plain,
% 2.62/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_927,c_937]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3498,plain,
% 2.62/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3491,c_2178]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3571,plain,
% 2.62/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 2.62/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3498,c_4]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3774,plain,
% 2.62/1.00      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3561,c_292,c_3571]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3785,plain,
% 2.62/1.00      ( sK4 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_2139,c_3774]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1914,plain,
% 2.62/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_929,c_935]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3501,plain,
% 2.62/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3491,c_1914]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3556,plain,
% 2.62/1.00      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3501,c_4]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_2177,plain,
% 2.62/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_929,c_937]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3499,plain,
% 2.62/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top
% 2.62/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3491,c_2177]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3566,plain,
% 2.62/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 2.62/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.62/1.00      inference(demodulation,[status(thm)],[c_3499,c_4]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3755,plain,
% 2.62/1.00      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.62/1.00      inference(global_propositional_subsumption,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3556,c_292,c_3566]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_3766,plain,
% 2.62/1.00      ( sK5 = k1_xboole_0 ),
% 2.62/1.00      inference(superposition,[status(thm)],[c_2139,c_3755]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1270,plain,
% 2.62/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_576]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1538,plain,
% 2.62/1.00      ( sK5 != X0 | sK5 = sK4 | sK4 != X0 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(c_1545,plain,
% 2.62/1.00      ( sK5 = sK4 | sK5 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.62/1.00      inference(instantiation,[status(thm)],[c_1538]) ).
% 2.62/1.00  
% 2.62/1.00  cnf(contradiction,plain,
% 2.62/1.00      ( $false ),
% 2.62/1.00      inference(minisat,
% 2.62/1.00                [status(thm)],
% 2.62/1.00                [c_3785,c_3766,c_1707,c_1545,c_1535,c_1332,c_23]) ).
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/1.00  
% 2.62/1.00  ------                               Statistics
% 2.62/1.00  
% 2.62/1.00  ------ General
% 2.62/1.00  
% 2.62/1.00  abstr_ref_over_cycles:                  0
% 2.62/1.00  abstr_ref_under_cycles:                 0
% 2.62/1.00  gc_basic_clause_elim:                   0
% 2.62/1.00  forced_gc_time:                         0
% 2.62/1.00  parsing_time:                           0.009
% 2.62/1.00  unif_index_cands_time:                  0.
% 2.62/1.00  unif_index_add_time:                    0.
% 2.62/1.00  orderings_time:                         0.
% 2.62/1.00  out_proof_time:                         0.02
% 2.62/1.00  total_time:                             0.153
% 2.62/1.00  num_of_symbols:                         50
% 2.62/1.00  num_of_terms:                           3473
% 2.62/1.00  
% 2.62/1.00  ------ Preprocessing
% 2.62/1.00  
% 2.62/1.00  num_of_splits:                          0
% 2.62/1.00  num_of_split_atoms:                     0
% 2.62/1.00  num_of_reused_defs:                     0
% 2.62/1.00  num_eq_ax_congr_red:                    20
% 2.62/1.00  num_of_sem_filtered_clauses:            1
% 2.62/1.00  num_of_subtypes:                        0
% 2.62/1.00  monotx_restored_types:                  0
% 2.62/1.00  sat_num_of_epr_types:                   0
% 2.62/1.00  sat_num_of_non_cyclic_types:            0
% 2.62/1.00  sat_guarded_non_collapsed_types:        0
% 2.62/1.00  num_pure_diseq_elim:                    0
% 2.62/1.00  simp_replaced_by:                       0
% 2.62/1.00  res_preprocessed:                       123
% 2.62/1.00  prep_upred:                             0
% 2.62/1.00  prep_unflattend:                        38
% 2.62/1.00  smt_new_axioms:                         0
% 2.62/1.00  pred_elim_cands:                        4
% 2.62/1.00  pred_elim:                              3
% 2.62/1.00  pred_elim_cl:                           4
% 2.62/1.00  pred_elim_cycles:                       5
% 2.62/1.00  merged_defs:                            0
% 2.62/1.00  merged_defs_ncl:                        0
% 2.62/1.00  bin_hyper_res:                          0
% 2.62/1.00  prep_cycles:                            4
% 2.62/1.00  pred_elim_time:                         0.004
% 2.62/1.00  splitting_time:                         0.
% 2.62/1.00  sem_filter_time:                        0.
% 2.62/1.00  monotx_time:                            0.
% 2.62/1.00  subtype_inf_time:                       0.
% 2.62/1.00  
% 2.62/1.00  ------ Problem properties
% 2.62/1.00  
% 2.62/1.00  clauses:                                25
% 2.62/1.00  conjectures:                            5
% 2.62/1.00  epr:                                    3
% 2.62/1.00  horn:                                   18
% 2.62/1.00  ground:                                 10
% 2.62/1.00  unary:                                  8
% 2.62/1.00  binary:                                 6
% 2.62/1.00  lits:                                   63
% 2.62/1.00  lits_eq:                                29
% 2.62/1.00  fd_pure:                                0
% 2.62/1.00  fd_pseudo:                              0
% 2.62/1.00  fd_cond:                                1
% 2.62/1.00  fd_pseudo_cond:                         4
% 2.62/1.00  ac_symbols:                             0
% 2.62/1.00  
% 2.62/1.00  ------ Propositional Solver
% 2.62/1.00  
% 2.62/1.00  prop_solver_calls:                      28
% 2.62/1.00  prop_fast_solver_calls:                 831
% 2.62/1.00  smt_solver_calls:                       0
% 2.62/1.00  smt_fast_solver_calls:                  0
% 2.62/1.00  prop_num_of_clauses:                    1404
% 2.62/1.00  prop_preprocess_simplified:             4424
% 2.62/1.00  prop_fo_subsumed:                       24
% 2.62/1.00  prop_solver_time:                       0.
% 2.62/1.00  smt_solver_time:                        0.
% 2.62/1.00  smt_fast_solver_time:                   0.
% 2.62/1.00  prop_fast_solver_time:                  0.
% 2.62/1.00  prop_unsat_core_time:                   0.
% 2.62/1.00  
% 2.62/1.00  ------ QBF
% 2.62/1.00  
% 2.62/1.00  qbf_q_res:                              0
% 2.62/1.00  qbf_num_tautologies:                    0
% 2.62/1.00  qbf_prep_cycles:                        0
% 2.62/1.00  
% 2.62/1.00  ------ BMC1
% 2.62/1.00  
% 2.62/1.00  bmc1_current_bound:                     -1
% 2.62/1.00  bmc1_last_solved_bound:                 -1
% 2.62/1.00  bmc1_unsat_core_size:                   -1
% 2.62/1.00  bmc1_unsat_core_parents_size:           -1
% 2.62/1.00  bmc1_merge_next_fun:                    0
% 2.62/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.62/1.00  
% 2.62/1.00  ------ Instantiation
% 2.62/1.00  
% 2.62/1.00  inst_num_of_clauses:                    455
% 2.62/1.00  inst_num_in_passive:                    96
% 2.62/1.00  inst_num_in_active:                     223
% 2.62/1.00  inst_num_in_unprocessed:                136
% 2.62/1.00  inst_num_of_loops:                      300
% 2.62/1.00  inst_num_of_learning_restarts:          0
% 2.62/1.00  inst_num_moves_active_passive:          73
% 2.62/1.00  inst_lit_activity:                      0
% 2.62/1.00  inst_lit_activity_moves:                0
% 2.62/1.00  inst_num_tautologies:                   0
% 2.62/1.00  inst_num_prop_implied:                  0
% 2.62/1.00  inst_num_existing_simplified:           0
% 2.62/1.00  inst_num_eq_res_simplified:             0
% 2.62/1.00  inst_num_child_elim:                    0
% 2.62/1.00  inst_num_of_dismatching_blockings:      58
% 2.62/1.00  inst_num_of_non_proper_insts:           318
% 2.62/1.00  inst_num_of_duplicates:                 0
% 2.62/1.00  inst_inst_num_from_inst_to_res:         0
% 2.62/1.00  inst_dismatching_checking_time:         0.
% 2.62/1.00  
% 2.62/1.00  ------ Resolution
% 2.62/1.00  
% 2.62/1.00  res_num_of_clauses:                     0
% 2.62/1.00  res_num_in_passive:                     0
% 2.62/1.00  res_num_in_active:                      0
% 2.62/1.00  res_num_of_loops:                       127
% 2.62/1.00  res_forward_subset_subsumed:            32
% 2.62/1.00  res_backward_subset_subsumed:           0
% 2.62/1.00  res_forward_subsumed:                   0
% 2.62/1.00  res_backward_subsumed:                  0
% 2.62/1.00  res_forward_subsumption_resolution:     0
% 2.62/1.00  res_backward_subsumption_resolution:    0
% 2.62/1.00  res_clause_to_clause_subsumption:       128
% 2.62/1.00  res_orphan_elimination:                 0
% 2.62/1.00  res_tautology_del:                      24
% 2.62/1.00  res_num_eq_res_simplified:              0
% 2.62/1.00  res_num_sel_changes:                    0
% 2.62/1.00  res_moves_from_active_to_pass:          0
% 2.62/1.00  
% 2.62/1.00  ------ Superposition
% 2.62/1.00  
% 2.62/1.00  sup_time_total:                         0.
% 2.62/1.00  sup_time_generating:                    0.
% 2.62/1.00  sup_time_sim_full:                      0.
% 2.62/1.00  sup_time_sim_immed:                     0.
% 2.62/1.00  
% 2.62/1.00  sup_num_of_clauses:                     56
% 2.62/1.00  sup_num_in_active:                      38
% 2.62/1.00  sup_num_in_passive:                     18
% 2.62/1.00  sup_num_of_loops:                       59
% 2.62/1.00  sup_fw_superposition:                   58
% 2.62/1.00  sup_bw_superposition:                   32
% 2.62/1.00  sup_immediate_simplified:               18
% 2.62/1.00  sup_given_eliminated:                   2
% 2.62/1.00  comparisons_done:                       0
% 2.62/1.00  comparisons_avoided:                    21
% 2.62/1.00  
% 2.62/1.00  ------ Simplifications
% 2.62/1.00  
% 2.62/1.00  
% 2.62/1.00  sim_fw_subset_subsumed:                 2
% 2.62/1.00  sim_bw_subset_subsumed:                 6
% 2.62/1.00  sim_fw_subsumed:                        5
% 2.62/1.00  sim_bw_subsumed:                        0
% 2.62/1.00  sim_fw_subsumption_res:                 4
% 2.62/1.00  sim_bw_subsumption_res:                 0
% 2.62/1.00  sim_tautology_del:                      2
% 2.62/1.00  sim_eq_tautology_del:                   23
% 2.62/1.00  sim_eq_res_simp:                        2
% 2.62/1.00  sim_fw_demodulated:                     13
% 2.62/1.00  sim_bw_demodulated:                     21
% 2.62/1.00  sim_light_normalised:                   0
% 2.62/1.00  sim_joinable_taut:                      0
% 2.62/1.00  sim_joinable_simp:                      0
% 2.62/1.00  sim_ac_normalised:                      0
% 2.62/1.00  sim_smt_subsumption:                    0
% 2.62/1.00  
%------------------------------------------------------------------------------
