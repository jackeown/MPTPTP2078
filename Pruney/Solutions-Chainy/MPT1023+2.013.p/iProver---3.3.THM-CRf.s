%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:43 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 784 expanded)
%              Number of clauses        :   88 ( 267 expanded)
%              Number of leaves         :   19 ( 198 expanded)
%              Depth                    :   23
%              Number of atoms          :  466 (4716 expanded)
%              Number of equality atoms :  217 ( 973 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f30,plain,(
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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f32,f31])).

fof(f55,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_400,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_19])).

cnf(c_961,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_963,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1907,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_961,c_963])).

cnf(c_2134,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_400,c_1907])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_411,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_22])).

cnf(c_959,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1908,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_959,c_963])).

cnf(c_2137,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_411,c_1908])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_966,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2404,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2134,c_966])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_267,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1133,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1153,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1152])).

cnf(c_1223,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1225,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_609,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1318,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1320,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_607,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1516,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_1687,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1956,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_964])).

cnf(c_1971,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1956])).

cnf(c_1957,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_964])).

cnf(c_1972,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1957])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1189,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_2658,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0 != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_2660,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_2690,plain,
    ( v1_funct_1(X0) != iProver_top
    | sK4 = X0
    | k1_relat_1(X0) != sK1
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2404,c_28,c_19,c_30,c_0,c_267,c_1133,c_1153,c_1225,c_1320,c_1687,c_1971,c_1972,c_2660])).

cnf(c_2691,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2690])).

cnf(c_2702,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_2691])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1155,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1156,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_2715,plain,
    ( sK4 = sK3
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2702,c_25,c_27,c_19,c_0,c_267,c_1133,c_1156,c_1225,c_1320,c_1687,c_1971,c_1972,c_2660])).

cnf(c_2721,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_2715])).

cnf(c_1297,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_608,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1172,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1551,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_19])).

cnf(c_2737,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_2847,plain,
    ( r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2721,c_19,c_0,c_267,c_1133,c_1225,c_1297,c_1320,c_1551,c_1687,c_1971,c_1972,c_2660,c_2737])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_969,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_980,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_969,c_2])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_968,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1982,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_968])).

cnf(c_2852,plain,
    ( m1_subset_1(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_1982])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_962,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3118,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2852,c_962])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_967,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3120,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_967])).

cnf(c_3172,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_25,c_27,c_28,c_19,c_30,c_1153,c_1156,c_1297,c_1551,c_2737])).

cnf(c_3175,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2134,c_3172])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3175,c_2737,c_2137,c_1972,c_1971,c_1320,c_1133,c_0,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.63/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/1.00  
% 2.63/1.00  ------  iProver source info
% 2.63/1.00  
% 2.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/1.00  git: non_committed_changes: false
% 2.63/1.00  git: last_make_outside_of_git: false
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     num_symb
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       true
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  ------ Parsing...
% 2.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/1.00  ------ Proving...
% 2.63/1.00  ------ Problem Properties 
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  clauses                                 22
% 2.63/1.00  conjectures                             5
% 2.63/1.00  EPR                                     4
% 2.63/1.00  Horn                                    17
% 2.63/1.00  unary                                   7
% 2.63/1.00  binary                                  6
% 2.63/1.00  lits                                    56
% 2.63/1.00  lits eq                                 24
% 2.63/1.00  fd_pure                                 0
% 2.63/1.00  fd_pseudo                               0
% 2.63/1.00  fd_cond                                 0
% 2.63/1.00  fd_pseudo_cond                          3
% 2.63/1.00  AC symbols                              0
% 2.63/1.00  
% 2.63/1.00  ------ Schedule dynamic 5 is on 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  Current options:
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     none
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       false
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ Proving...
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS status Theorem for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  fof(f11,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f24,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(ennf_transformation,[],[f11])).
% 2.63/1.00  
% 2.63/1.00  fof(f25,plain,(
% 2.63/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(flattening,[],[f24])).
% 2.63/1.00  
% 2.63/1.00  fof(f30,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(nnf_transformation,[],[f25])).
% 2.63/1.00  
% 2.63/1.00  fof(f45,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f30])).
% 2.63/1.00  
% 2.63/1.00  fof(f12,conjecture,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f13,negated_conjecture,(
% 2.63/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.63/1.00    inference(negated_conjecture,[],[f12])).
% 2.63/1.00  
% 2.63/1.00  fof(f26,plain,(
% 2.63/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f13])).
% 2.63/1.00  
% 2.63/1.00  fof(f27,plain,(
% 2.63/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f26])).
% 2.63/1.00  
% 2.63/1.00  fof(f32,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f31,plain,(
% 2.63/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f33,plain,(
% 2.63/1.00    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f32,f31])).
% 2.63/1.00  
% 2.63/1.00  fof(f55,plain,(
% 2.63/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f56,plain,(
% 2.63/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f9,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f21,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(ennf_transformation,[],[f9])).
% 2.63/1.00  
% 2.63/1.00  fof(f43,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f21])).
% 2.63/1.00  
% 2.63/1.00  fof(f52,plain,(
% 2.63/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f53,plain,(
% 2.63/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f6,axiom,(
% 2.63/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f17,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f6])).
% 2.63/1.00  
% 2.63/1.00  fof(f18,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(flattening,[],[f17])).
% 2.63/1.00  
% 2.63/1.00  fof(f28,plain,(
% 2.63/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f29,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).
% 2.63/1.00  
% 2.63/1.00  fof(f39,plain,(
% 2.63/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  fof(f54,plain,(
% 2.63/1.00    v1_funct_1(sK4)),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f1,axiom,(
% 2.63/1.00    v1_xboole_0(k1_xboole_0)),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f34,plain,(
% 2.63/1.00    v1_xboole_0(k1_xboole_0)),
% 2.63/1.00    inference(cnf_transformation,[],[f1])).
% 2.63/1.00  
% 2.63/1.00  fof(f10,axiom,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f22,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.63/1.00    inference(ennf_transformation,[],[f10])).
% 2.63/1.00  
% 2.63/1.00  fof(f23,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(flattening,[],[f22])).
% 2.63/1.00  
% 2.63/1.00  fof(f44,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f23])).
% 2.63/1.00  
% 2.63/1.00  fof(f58,plain,(
% 2.63/1.00    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f2,axiom,(
% 2.63/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f14,plain,(
% 2.63/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f2])).
% 2.63/1.00  
% 2.63/1.00  fof(f35,plain,(
% 2.63/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f14])).
% 2.63/1.00  
% 2.63/1.00  fof(f7,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f19,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(ennf_transformation,[],[f7])).
% 2.63/1.00  
% 2.63/1.00  fof(f41,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f8,axiom,(
% 2.63/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f20,plain,(
% 2.63/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f8])).
% 2.63/1.00  
% 2.63/1.00  fof(f42,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f20])).
% 2.63/1.00  
% 2.63/1.00  fof(f51,plain,(
% 2.63/1.00    v1_funct_1(sK3)),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f4,axiom,(
% 2.63/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f37,plain,(
% 2.63/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f4])).
% 2.63/1.00  
% 2.63/1.00  fof(f3,axiom,(
% 2.63/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f36,plain,(
% 2.63/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.63/1.00    inference(cnf_transformation,[],[f3])).
% 2.63/1.00  
% 2.63/1.00  fof(f5,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f15,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.63/1.00    inference(ennf_transformation,[],[f5])).
% 2.63/1.00  
% 2.63/1.00  fof(f16,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.63/1.00    inference(flattening,[],[f15])).
% 2.63/1.00  
% 2.63/1.00  fof(f38,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f16])).
% 2.63/1.00  
% 2.63/1.00  fof(f57,plain,(
% 2.63/1.00    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f40,plain,(
% 2.63/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  cnf(c_16,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_20,negated_conjecture,
% 2.63/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.63/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_397,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.63/1.00      | sK4 != X0
% 2.63/1.00      | sK2 != X2
% 2.63/1.00      | sK1 != X1
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_398,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.63/1.00      | k1_xboole_0 = sK2 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_19,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_400,plain,
% 2.63/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_398,c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_961,plain,
% 2.63/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_9,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_963,plain,
% 2.63/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.63/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1907,plain,
% 2.63/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_961,c_963]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2134,plain,
% 2.63/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_400,c_1907]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_23,negated_conjecture,
% 2.63/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.63/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_408,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.63/1.00      | sK3 != X0
% 2.63/1.00      | sK2 != X2
% 2.63/1.00      | sK1 != X1
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_409,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.63/1.00      | k1_xboole_0 = sK2 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_22,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_411,plain,
% 2.63/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_409,c_22]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_959,plain,
% 2.63/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1908,plain,
% 2.63/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_959,c_963]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2137,plain,
% 2.63/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_411,c_1908]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_6,plain,
% 2.63/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.63/1.00      | ~ v1_relat_1(X1)
% 2.63/1.00      | ~ v1_relat_1(X0)
% 2.63/1.00      | ~ v1_funct_1(X1)
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | X0 = X1
% 2.63/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_966,plain,
% 2.63/1.00      ( X0 = X1
% 2.63/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.63/1.00      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.63/1.00      | v1_relat_1(X0) != iProver_top
% 2.63/1.00      | v1_relat_1(X1) != iProver_top
% 2.63/1.00      | v1_funct_1(X1) != iProver_top
% 2.63/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2404,plain,
% 2.63/1.00      ( k1_relat_1(X0) != sK1
% 2.63/1.00      | sK4 = X0
% 2.63/1.00      | sK2 = k1_xboole_0
% 2.63/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.63/1.00      | v1_relat_1(X0) != iProver_top
% 2.63/1.00      | v1_relat_1(sK4) != iProver_top
% 2.63/1.00      | v1_funct_1(X0) != iProver_top
% 2.63/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2134,c_966]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_21,negated_conjecture,
% 2.63/1.00      ( v1_funct_1(sK4) ),
% 2.63/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_28,plain,
% 2.63/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_30,plain,
% 2.63/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_0,plain,
% 2.63/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_10,plain,
% 2.63/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.63/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_17,negated_conjecture,
% 2.63/1.00      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 2.63/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_264,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | sK4 != X0
% 2.63/1.00      | sK3 != X0
% 2.63/1.00      | sK2 != X2
% 2.63/1.00      | sK1 != X1 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_265,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | sK3 != sK4 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_267,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | sK3 != sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_265]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1,plain,
% 2.63/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.63/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1133,plain,
% 2.63/1.00      ( ~ v1_xboole_0(sK4) | ~ v1_xboole_0(sK3) | sK3 = sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_7,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | v1_relat_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1152,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | v1_relat_1(sK4) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1153,plain,
% 2.63/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.63/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1152]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1223,plain,
% 2.63/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK4) | X0 = sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1225,plain,
% 2.63/1.00      ( ~ v1_xboole_0(sK4)
% 2.63/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.63/1.00      | k1_xboole_0 = sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1223]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_609,plain,
% 2.63/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.63/1.00      theory(equality) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1318,plain,
% 2.63/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_609]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1320,plain,
% 2.63/1.00      ( v1_xboole_0(sK2)
% 2.63/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.63/1.00      | sK2 != k1_xboole_0 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1318]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_607,plain,( X0 = X0 ),theory(equality) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1516,plain,
% 2.63/1.00      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_607]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1687,plain,
% 2.63/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1516]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | ~ v1_xboole_0(X2)
% 2.63/1.00      | v1_xboole_0(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_964,plain,
% 2.63/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.63/1.00      | v1_xboole_0(X2) != iProver_top
% 2.63/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1956,plain,
% 2.63/1.00      ( v1_xboole_0(sK4) = iProver_top
% 2.63/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_961,c_964]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1971,plain,
% 2.63/1.00      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 2.63/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1956]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1957,plain,
% 2.63/1.00      ( v1_xboole_0(sK3) = iProver_top
% 2.63/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_959,c_964]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1972,plain,
% 2.63/1.00      ( v1_xboole_0(sK3) | ~ v1_xboole_0(sK2) ),
% 2.63/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1957]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_611,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.63/1.00      theory(equality) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1189,plain,
% 2.63/1.00      ( m1_subset_1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.63/1.00      | X0 != sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_611]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2658,plain,
% 2.63/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | X0 != sK4
% 2.63/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1189]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2660,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.63/1.00      | k1_xboole_0 != sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_2658]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2690,plain,
% 2.63/1.00      ( v1_funct_1(X0) != iProver_top
% 2.63/1.00      | sK4 = X0
% 2.63/1.00      | k1_relat_1(X0) != sK1
% 2.63/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.63/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2404,c_28,c_19,c_30,c_0,c_267,c_1133,c_1153,c_1225,
% 2.63/1.00                 c_1320,c_1687,c_1971,c_1972,c_2660]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2691,plain,
% 2.63/1.00      ( k1_relat_1(X0) != sK1
% 2.63/1.00      | sK4 = X0
% 2.63/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.63/1.00      | v1_relat_1(X0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_2690]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2702,plain,
% 2.63/1.00      ( sK4 = sK3
% 2.63/1.00      | sK2 = k1_xboole_0
% 2.63/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 2.63/1.00      | v1_relat_1(sK3) != iProver_top
% 2.63/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2137,c_2691]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_24,negated_conjecture,
% 2.63/1.00      ( v1_funct_1(sK3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_25,plain,
% 2.63/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_27,plain,
% 2.63/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1155,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | v1_relat_1(sK3) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1156,plain,
% 2.63/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.63/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2715,plain,
% 2.63/1.00      ( sK4 = sK3
% 2.63/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2702,c_25,c_27,c_19,c_0,c_267,c_1133,c_1156,c_1225,
% 2.63/1.00                 c_1320,c_1687,c_1971,c_1972,c_2660]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2721,plain,
% 2.63/1.00      ( sK4 = sK3
% 2.63/1.00      | sK2 = k1_xboole_0
% 2.63/1.00      | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2137,c_2715]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1297,plain,
% 2.63/1.00      ( sK3 = sK3 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_607]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_608,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1172,plain,
% 2.63/1.00      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_608]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1551,plain,
% 2.63/1.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1172]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_269,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | sK3 != sK4 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_265,c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2737,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.63/1.00      | sK3 != sK4 ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_269]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2847,plain,
% 2.63/1.00      ( r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2721,c_19,c_0,c_267,c_1133,c_1225,c_1297,c_1320,
% 2.63/1.00                 c_1551,c_1687,c_1971,c_1972,c_2660,c_2737]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3,plain,
% 2.63/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_969,plain,
% 2.63/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2,plain,
% 2.63/1.00      ( k2_subset_1(X0) = X0 ),
% 2.63/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_980,plain,
% 2.63/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_969,c_2]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4,plain,
% 2.63/1.00      ( ~ r2_hidden(X0,X1)
% 2.63/1.00      | m1_subset_1(X0,X2)
% 2.63/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_968,plain,
% 2.63/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.63/1.00      | m1_subset_1(X0,X2) = iProver_top
% 2.63/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1982,plain,
% 2.63/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.63/1.00      | m1_subset_1(X0,X1) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_980,c_968]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2852,plain,
% 2.63/1.00      ( m1_subset_1(sK0(sK3,sK4),sK1) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2847,c_1982]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_18,negated_conjecture,
% 2.63/1.00      ( ~ m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_962,plain,
% 2.63/1.00      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.63/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3118,plain,
% 2.63/1.00      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2852,c_962]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5,plain,
% 2.63/1.00      ( ~ v1_relat_1(X0)
% 2.63/1.00      | ~ v1_relat_1(X1)
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | ~ v1_funct_1(X1)
% 2.63/1.00      | X1 = X0
% 2.63/1.00      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.63/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_967,plain,
% 2.63/1.00      ( X0 = X1
% 2.63/1.00      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 2.63/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.63/1.00      | v1_relat_1(X1) != iProver_top
% 2.63/1.00      | v1_relat_1(X0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0) != iProver_top
% 2.63/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3120,plain,
% 2.63/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.63/1.00      | sK4 = sK3
% 2.63/1.00      | v1_relat_1(sK4) != iProver_top
% 2.63/1.00      | v1_relat_1(sK3) != iProver_top
% 2.63/1.00      | v1_funct_1(sK4) != iProver_top
% 2.63/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3118,c_967]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3172,plain,
% 2.63/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK4) ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3120,c_25,c_27,c_28,c_19,c_30,c_1153,c_1156,c_1297,
% 2.63/1.00                 c_1551,c_2737]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3175,plain,
% 2.63/1.00      ( k1_relat_1(sK3) != sK1 | sK2 = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2134,c_3172]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(contradiction,plain,
% 2.63/1.00      ( $false ),
% 2.63/1.00      inference(minisat,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3175,c_2737,c_2137,c_1972,c_1971,c_1320,c_1133,c_0,
% 2.63/1.00                 c_19]) ).
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  ------                               Statistics
% 2.63/1.00  
% 2.63/1.00  ------ General
% 2.63/1.00  
% 2.63/1.00  abstr_ref_over_cycles:                  0
% 2.63/1.00  abstr_ref_under_cycles:                 0
% 2.63/1.00  gc_basic_clause_elim:                   0
% 2.63/1.00  forced_gc_time:                         0
% 2.63/1.00  parsing_time:                           0.015
% 2.63/1.00  unif_index_cands_time:                  0.
% 2.63/1.00  unif_index_add_time:                    0.
% 2.63/1.00  orderings_time:                         0.
% 2.63/1.00  out_proof_time:                         0.012
% 2.63/1.00  total_time:                             0.146
% 2.63/1.00  num_of_symbols:                         50
% 2.63/1.00  num_of_terms:                           2622
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing
% 2.63/1.00  
% 2.63/1.00  num_of_splits:                          0
% 2.63/1.00  num_of_split_atoms:                     0
% 2.63/1.00  num_of_reused_defs:                     0
% 2.63/1.00  num_eq_ax_congr_red:                    17
% 2.63/1.00  num_of_sem_filtered_clauses:            1
% 2.63/1.00  num_of_subtypes:                        0
% 2.63/1.00  monotx_restored_types:                  0
% 2.63/1.00  sat_num_of_epr_types:                   0
% 2.63/1.00  sat_num_of_non_cyclic_types:            0
% 2.63/1.00  sat_guarded_non_collapsed_types:        0
% 2.63/1.00  num_pure_diseq_elim:                    0
% 2.63/1.00  simp_replaced_by:                       0
% 2.63/1.00  res_preprocessed:                       112
% 2.63/1.00  prep_upred:                             0
% 2.63/1.00  prep_unflattend:                        41
% 2.63/1.00  smt_new_axioms:                         0
% 2.63/1.00  pred_elim_cands:                        5
% 2.63/1.00  pred_elim:                              2
% 2.63/1.00  pred_elim_cl:                           3
% 2.63/1.00  pred_elim_cycles:                       5
% 2.63/1.00  merged_defs:                            0
% 2.63/1.00  merged_defs_ncl:                        0
% 2.63/1.00  bin_hyper_res:                          0
% 2.63/1.00  prep_cycles:                            4
% 2.63/1.00  pred_elim_time:                         0.005
% 2.63/1.00  splitting_time:                         0.
% 2.63/1.00  sem_filter_time:                        0.
% 2.63/1.00  monotx_time:                            0.001
% 2.63/1.00  subtype_inf_time:                       0.
% 2.63/1.00  
% 2.63/1.00  ------ Problem properties
% 2.63/1.00  
% 2.63/1.00  clauses:                                22
% 2.63/1.00  conjectures:                            5
% 2.63/1.00  epr:                                    4
% 2.63/1.00  horn:                                   17
% 2.63/1.00  ground:                                 11
% 2.63/1.00  unary:                                  7
% 2.63/1.00  binary:                                 6
% 2.63/1.00  lits:                                   56
% 2.63/1.00  lits_eq:                                24
% 2.63/1.00  fd_pure:                                0
% 2.63/1.00  fd_pseudo:                              0
% 2.63/1.00  fd_cond:                                0
% 2.63/1.00  fd_pseudo_cond:                         3
% 2.63/1.00  ac_symbols:                             0
% 2.63/1.00  
% 2.63/1.00  ------ Propositional Solver
% 2.63/1.00  
% 2.63/1.00  prop_solver_calls:                      26
% 2.63/1.00  prop_fast_solver_calls:                 793
% 2.63/1.00  smt_solver_calls:                       0
% 2.63/1.00  smt_fast_solver_calls:                  0
% 2.63/1.00  prop_num_of_clauses:                    1017
% 2.63/1.00  prop_preprocess_simplified:             3759
% 2.63/1.00  prop_fo_subsumed:                       30
% 2.63/1.00  prop_solver_time:                       0.
% 2.63/1.00  smt_solver_time:                        0.
% 2.63/1.00  smt_fast_solver_time:                   0.
% 2.63/1.00  prop_fast_solver_time:                  0.
% 2.63/1.00  prop_unsat_core_time:                   0.
% 2.63/1.00  
% 2.63/1.00  ------ QBF
% 2.63/1.00  
% 2.63/1.00  qbf_q_res:                              0
% 2.63/1.00  qbf_num_tautologies:                    0
% 2.63/1.00  qbf_prep_cycles:                        0
% 2.63/1.00  
% 2.63/1.00  ------ BMC1
% 2.63/1.00  
% 2.63/1.00  bmc1_current_bound:                     -1
% 2.63/1.00  bmc1_last_solved_bound:                 -1
% 2.63/1.00  bmc1_unsat_core_size:                   -1
% 2.63/1.00  bmc1_unsat_core_parents_size:           -1
% 2.63/1.00  bmc1_merge_next_fun:                    0
% 2.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation
% 2.63/1.00  
% 2.63/1.00  inst_num_of_clauses:                    315
% 2.63/1.00  inst_num_in_passive:                    89
% 2.63/1.00  inst_num_in_active:                     198
% 2.63/1.00  inst_num_in_unprocessed:                28
% 2.63/1.00  inst_num_of_loops:                      250
% 2.63/1.00  inst_num_of_learning_restarts:          0
% 2.63/1.00  inst_num_moves_active_passive:          49
% 2.63/1.00  inst_lit_activity:                      0
% 2.63/1.00  inst_lit_activity_moves:                0
% 2.63/1.00  inst_num_tautologies:                   0
% 2.63/1.00  inst_num_prop_implied:                  0
% 2.63/1.00  inst_num_existing_simplified:           0
% 2.63/1.00  inst_num_eq_res_simplified:             0
% 2.63/1.00  inst_num_child_elim:                    0
% 2.63/1.00  inst_num_of_dismatching_blockings:      125
% 2.63/1.00  inst_num_of_non_proper_insts:           413
% 2.63/1.00  inst_num_of_duplicates:                 0
% 2.63/1.00  inst_inst_num_from_inst_to_res:         0
% 2.63/1.00  inst_dismatching_checking_time:         0.
% 2.63/1.00  
% 2.63/1.00  ------ Resolution
% 2.63/1.00  
% 2.63/1.00  res_num_of_clauses:                     0
% 2.63/1.00  res_num_in_passive:                     0
% 2.63/1.00  res_num_in_active:                      0
% 2.63/1.00  res_num_of_loops:                       116
% 2.63/1.00  res_forward_subset_subsumed:            44
% 2.63/1.00  res_backward_subset_subsumed:           0
% 2.63/1.00  res_forward_subsumed:                   0
% 2.63/1.00  res_backward_subsumed:                  0
% 2.63/1.00  res_forward_subsumption_resolution:     0
% 2.63/1.00  res_backward_subsumption_resolution:    0
% 2.63/1.00  res_clause_to_clause_subsumption:       82
% 2.63/1.00  res_orphan_elimination:                 0
% 2.63/1.00  res_tautology_del:                      44
% 2.63/1.00  res_num_eq_res_simplified:              0
% 2.63/1.00  res_num_sel_changes:                    0
% 2.63/1.00  res_moves_from_active_to_pass:          0
% 2.63/1.00  
% 2.63/1.00  ------ Superposition
% 2.63/1.00  
% 2.63/1.00  sup_time_total:                         0.
% 2.63/1.00  sup_time_generating:                    0.
% 2.63/1.00  sup_time_sim_full:                      0.
% 2.63/1.00  sup_time_sim_immed:                     0.
% 2.63/1.00  
% 2.63/1.00  sup_num_of_clauses:                     58
% 2.63/1.00  sup_num_in_active:                      49
% 2.63/1.00  sup_num_in_passive:                     9
% 2.63/1.00  sup_num_of_loops:                       48
% 2.63/1.00  sup_fw_superposition:                   29
% 2.63/1.00  sup_bw_superposition:                   14
% 2.63/1.00  sup_immediate_simplified:               2
% 2.63/1.00  sup_given_eliminated:                   0
% 2.63/1.00  comparisons_done:                       0
% 2.63/1.00  comparisons_avoided:                    6
% 2.63/1.00  
% 2.63/1.00  ------ Simplifications
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  sim_fw_subset_subsumed:                 1
% 2.63/1.00  sim_bw_subset_subsumed:                 0
% 2.63/1.00  sim_fw_subsumed:                        1
% 2.63/1.00  sim_bw_subsumed:                        0
% 2.63/1.00  sim_fw_subsumption_res:                 0
% 2.63/1.00  sim_bw_subsumption_res:                 0
% 2.63/1.00  sim_tautology_del:                      0
% 2.63/1.00  sim_eq_tautology_del:                   7
% 2.63/1.00  sim_eq_res_simp:                        0
% 2.63/1.00  sim_fw_demodulated:                     0
% 2.63/1.00  sim_bw_demodulated:                     0
% 2.63/1.00  sim_light_normalised:                   1
% 2.63/1.00  sim_joinable_taut:                      0
% 2.63/1.00  sim_joinable_simp:                      0
% 2.63/1.00  sim_ac_normalised:                      0
% 2.63/1.00  sim_smt_subsumption:                    0
% 2.63/1.00  
%------------------------------------------------------------------------------
