%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:17 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  176 (2899 expanded)
%              Number of clauses        :  118 ( 965 expanded)
%              Number of leaves         :   15 ( 676 expanded)
%              Depth                    :   31
%              Number of atoms          :  634 (17990 expanded)
%              Number of equality atoms :  381 (4620 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f33,f32])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f64,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2293,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3866,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2293,c_2299])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_208])).

cnf(c_2289,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_5030,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3866,c_2289])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2298,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5127,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5030,c_2298])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_914,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_915,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_917,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_915,c_27])).

cnf(c_2291,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2295,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2640,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2291,c_2295])).

cnf(c_2906,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_917,c_2640])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_903,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_904,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_906,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_24])).

cnf(c_2639,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2293,c_2295])).

cnf(c_2850,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_906,c_2639])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2296,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3090,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_2296])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3278,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | sK2 = k1_xboole_0
    | sK4 = X0
    | k1_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3090,c_33])).

cnf(c_3279,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3278])).

cnf(c_3292,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_3279])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3339,plain,
    ( r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | sK2 = k1_xboole_0
    | sK4 = sK3
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_30])).

cnf(c_3340,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3339])).

cnf(c_3348,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_3340])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2294,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3356,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_2294])).

cnf(c_5130,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5127,c_3356])).

cnf(c_3091,plain,
    ( k1_relat_1(X0) != sK1
    | sK3 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_2296])).

cnf(c_3421,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | sK2 = k1_xboole_0
    | sK3 = X0
    | k1_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3091,c_30])).

cnf(c_3422,plain,
    ( k1_relat_1(X0) != sK1
    | sK3 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3421])).

cnf(c_3434,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_3422])).

cnf(c_3620,plain,
    ( r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | sK2 = k1_xboole_0
    | sK4 = sK3
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3434,c_33])).

cnf(c_3621,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3620])).

cnf(c_3629,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_3621])).

cnf(c_3637,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_2294])).

cnf(c_5129,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5127,c_3637])).

cnf(c_3638,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3637])).

cnf(c_5128,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5127])).

cnf(c_3867,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_2299])).

cnf(c_5031,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3867,c_2289])).

cnf(c_5152,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5031,c_2298])).

cnf(c_5153,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5152])).

cnf(c_5278,plain,
    ( sK2 = k1_xboole_0
    | sK4 = sK3
    | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5129,c_3638,c_5128,c_5153])).

cnf(c_5279,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5278])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2297,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5283,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5279,c_2297])).

cnf(c_5284,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5283])).

cnf(c_5286,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5283,c_29,c_26,c_5128,c_5153,c_5284])).

cnf(c_5291,plain,
    ( k1_relat_1(sK3) != sK1
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2850,c_5286])).

cnf(c_5376,plain,
    ( sK2 = k1_xboole_0
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5130,c_2906,c_5291])).

cnf(c_5377,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5376])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_363,plain,
    ( sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_24])).

cnf(c_5394,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5377,c_363])).

cnf(c_5416,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5394,c_2293])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5422,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5416,c_4])).

cnf(c_5417,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5394,c_2291])).

cnf(c_5419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5417,c_4])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_842,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_2288,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2389,plain,
    ( sK4 = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2288,c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2661,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2662,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_2664,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2780,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2783,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2780])).

cnf(c_2997,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2998,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_3000,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3076,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_2664,c_2783,c_3000])).

cnf(c_857,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_2287,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2380,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2287,c_4])).

cnf(c_2808,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2811,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_2822,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2823,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_2825,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_3013,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3014,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_3016,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3032,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_2811,c_2825,c_3016])).

cnf(c_1778,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2500,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_2501,plain,
    ( sK4 != k1_xboole_0
    | sK3 = sK4
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5422,c_5419,c_3076,c_3032,c_2501,c_361,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.56/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.00  
% 2.56/1.00  ------  iProver source info
% 2.56/1.00  
% 2.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.00  git: non_committed_changes: false
% 2.56/1.00  git: last_make_outside_of_git: false
% 2.56/1.00  
% 2.56/1.00  ------ 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options
% 2.56/1.00  
% 2.56/1.00  --out_options                           all
% 2.56/1.00  --tptp_safe_out                         true
% 2.56/1.00  --problem_path                          ""
% 2.56/1.00  --include_path                          ""
% 2.56/1.00  --clausifier                            res/vclausify_rel
% 2.56/1.00  --clausifier_options                    --mode clausify
% 2.56/1.00  --stdin                                 false
% 2.56/1.00  --stats_out                             all
% 2.56/1.00  
% 2.56/1.00  ------ General Options
% 2.56/1.00  
% 2.56/1.00  --fof                                   false
% 2.56/1.00  --time_out_real                         305.
% 2.56/1.00  --time_out_virtual                      -1.
% 2.56/1.00  --symbol_type_check                     false
% 2.56/1.00  --clausify_out                          false
% 2.56/1.00  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     num_symb
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       true
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  ------ Parsing...
% 2.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.00  ------ Proving...
% 2.56/1.00  ------ Problem Properties 
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  clauses                                 25
% 2.56/1.00  conjectures                             5
% 2.56/1.00  EPR                                     7
% 2.56/1.00  Horn                                    19
% 2.56/1.00  unary                                   10
% 2.56/1.00  binary                                  6
% 2.56/1.00  lits                                    59
% 2.56/1.00  lits eq                                 28
% 2.56/1.00  fd_pure                                 0
% 2.56/1.00  fd_pseudo                               0
% 2.56/1.00  fd_cond                                 1
% 2.56/1.00  fd_pseudo_cond                          3
% 2.56/1.00  AC symbols                              0
% 2.56/1.00  
% 2.56/1.00  ------ Schedule dynamic 5 is on 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ 
% 2.56/1.00  Current options:
% 2.56/1.00  ------ 
% 2.56/1.00  
% 2.56/1.00  ------ Input Options
% 2.56/1.00  
% 2.56/1.00  --out_options                           all
% 2.56/1.00  --tptp_safe_out                         true
% 2.56/1.00  --problem_path                          ""
% 2.56/1.00  --include_path                          ""
% 2.56/1.00  --clausifier                            res/vclausify_rel
% 2.56/1.00  --clausifier_options                    --mode clausify
% 2.56/1.00  --stdin                                 false
% 2.56/1.00  --stats_out                             all
% 2.56/1.00  
% 2.56/1.00  ------ General Options
% 2.56/1.00  
% 2.56/1.00  --fof                                   false
% 2.56/1.00  --time_out_real                         305.
% 2.56/1.00  --time_out_virtual                      -1.
% 2.56/1.00  --symbol_type_check                     false
% 2.56/1.00  --clausify_out                          false
% 2.56/1.00  --sig_cnt_out                           false
% 2.56/1.00  --trig_cnt_out                          false
% 2.56/1.00  --trig_cnt_out_tolerance                1.
% 2.56/1.00  --trig_cnt_out_sk_spl                   false
% 2.56/1.00  --abstr_cl_out                          false
% 2.56/1.00  
% 2.56/1.00  ------ Global Options
% 2.56/1.00  
% 2.56/1.00  --schedule                              default
% 2.56/1.00  --add_important_lit                     false
% 2.56/1.00  --prop_solver_per_cl                    1000
% 2.56/1.00  --min_unsat_core                        false
% 2.56/1.00  --soft_assumptions                      false
% 2.56/1.00  --soft_lemma_size                       3
% 2.56/1.00  --prop_impl_unit_size                   0
% 2.56/1.00  --prop_impl_unit                        []
% 2.56/1.00  --share_sel_clauses                     true
% 2.56/1.00  --reset_solvers                         false
% 2.56/1.00  --bc_imp_inh                            [conj_cone]
% 2.56/1.00  --conj_cone_tolerance                   3.
% 2.56/1.00  --extra_neg_conj                        none
% 2.56/1.00  --large_theory_mode                     true
% 2.56/1.00  --prolific_symb_bound                   200
% 2.56/1.00  --lt_threshold                          2000
% 2.56/1.00  --clause_weak_htbl                      true
% 2.56/1.00  --gc_record_bc_elim                     false
% 2.56/1.00  
% 2.56/1.00  ------ Preprocessing Options
% 2.56/1.00  
% 2.56/1.00  --preprocessing_flag                    true
% 2.56/1.00  --time_out_prep_mult                    0.1
% 2.56/1.00  --splitting_mode                        input
% 2.56/1.00  --splitting_grd                         true
% 2.56/1.00  --splitting_cvd                         false
% 2.56/1.00  --splitting_cvd_svl                     false
% 2.56/1.00  --splitting_nvd                         32
% 2.56/1.00  --sub_typing                            true
% 2.56/1.00  --prep_gs_sim                           true
% 2.56/1.00  --prep_unflatten                        true
% 2.56/1.00  --prep_res_sim                          true
% 2.56/1.00  --prep_upred                            true
% 2.56/1.00  --prep_sem_filter                       exhaustive
% 2.56/1.00  --prep_sem_filter_out                   false
% 2.56/1.00  --pred_elim                             true
% 2.56/1.00  --res_sim_input                         true
% 2.56/1.00  --eq_ax_congr_red                       true
% 2.56/1.00  --pure_diseq_elim                       true
% 2.56/1.00  --brand_transform                       false
% 2.56/1.00  --non_eq_to_eq                          false
% 2.56/1.00  --prep_def_merge                        true
% 2.56/1.00  --prep_def_merge_prop_impl              false
% 2.56/1.00  --prep_def_merge_mbd                    true
% 2.56/1.00  --prep_def_merge_tr_red                 false
% 2.56/1.00  --prep_def_merge_tr_cl                  false
% 2.56/1.00  --smt_preprocessing                     true
% 2.56/1.00  --smt_ac_axioms                         fast
% 2.56/1.00  --preprocessed_out                      false
% 2.56/1.00  --preprocessed_stats                    false
% 2.56/1.00  
% 2.56/1.00  ------ Abstraction refinement Options
% 2.56/1.00  
% 2.56/1.00  --abstr_ref                             []
% 2.56/1.00  --abstr_ref_prep                        false
% 2.56/1.00  --abstr_ref_until_sat                   false
% 2.56/1.00  --abstr_ref_sig_restrict                funpre
% 2.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.00  --abstr_ref_under                       []
% 2.56/1.00  
% 2.56/1.00  ------ SAT Options
% 2.56/1.00  
% 2.56/1.00  --sat_mode                              false
% 2.56/1.00  --sat_fm_restart_options                ""
% 2.56/1.00  --sat_gr_def                            false
% 2.56/1.00  --sat_epr_types                         true
% 2.56/1.00  --sat_non_cyclic_types                  false
% 2.56/1.00  --sat_finite_models                     false
% 2.56/1.00  --sat_fm_lemmas                         false
% 2.56/1.00  --sat_fm_prep                           false
% 2.56/1.00  --sat_fm_uc_incr                        true
% 2.56/1.00  --sat_out_model                         small
% 2.56/1.00  --sat_out_clauses                       false
% 2.56/1.00  
% 2.56/1.00  ------ QBF Options
% 2.56/1.00  
% 2.56/1.00  --qbf_mode                              false
% 2.56/1.00  --qbf_elim_univ                         false
% 2.56/1.00  --qbf_dom_inst                          none
% 2.56/1.00  --qbf_dom_pre_inst                      false
% 2.56/1.00  --qbf_sk_in                             false
% 2.56/1.00  --qbf_pred_elim                         true
% 2.56/1.00  --qbf_split                             512
% 2.56/1.00  
% 2.56/1.00  ------ BMC1 Options
% 2.56/1.00  
% 2.56/1.00  --bmc1_incremental                      false
% 2.56/1.00  --bmc1_axioms                           reachable_all
% 2.56/1.00  --bmc1_min_bound                        0
% 2.56/1.00  --bmc1_max_bound                        -1
% 2.56/1.00  --bmc1_max_bound_default                -1
% 2.56/1.00  --bmc1_symbol_reachability              true
% 2.56/1.00  --bmc1_property_lemmas                  false
% 2.56/1.00  --bmc1_k_induction                      false
% 2.56/1.00  --bmc1_non_equiv_states                 false
% 2.56/1.00  --bmc1_deadlock                         false
% 2.56/1.00  --bmc1_ucm                              false
% 2.56/1.00  --bmc1_add_unsat_core                   none
% 2.56/1.00  --bmc1_unsat_core_children              false
% 2.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.00  --bmc1_out_stat                         full
% 2.56/1.00  --bmc1_ground_init                      false
% 2.56/1.00  --bmc1_pre_inst_next_state              false
% 2.56/1.00  --bmc1_pre_inst_state                   false
% 2.56/1.00  --bmc1_pre_inst_reach_state             false
% 2.56/1.00  --bmc1_out_unsat_core                   false
% 2.56/1.00  --bmc1_aig_witness_out                  false
% 2.56/1.00  --bmc1_verbose                          false
% 2.56/1.00  --bmc1_dump_clauses_tptp                false
% 2.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.00  --bmc1_dump_file                        -
% 2.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.00  --bmc1_ucm_extend_mode                  1
% 2.56/1.00  --bmc1_ucm_init_mode                    2
% 2.56/1.00  --bmc1_ucm_cone_mode                    none
% 2.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.00  --bmc1_ucm_relax_model                  4
% 2.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.00  --bmc1_ucm_layered_model                none
% 2.56/1.00  --bmc1_ucm_max_lemma_size               10
% 2.56/1.00  
% 2.56/1.00  ------ AIG Options
% 2.56/1.00  
% 2.56/1.00  --aig_mode                              false
% 2.56/1.00  
% 2.56/1.00  ------ Instantiation Options
% 2.56/1.00  
% 2.56/1.00  --instantiation_flag                    true
% 2.56/1.00  --inst_sos_flag                         false
% 2.56/1.00  --inst_sos_phase                        true
% 2.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.00  --inst_lit_sel_side                     none
% 2.56/1.00  --inst_solver_per_active                1400
% 2.56/1.00  --inst_solver_calls_frac                1.
% 2.56/1.00  --inst_passive_queue_type               priority_queues
% 2.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.00  --inst_passive_queues_freq              [25;2]
% 2.56/1.00  --inst_dismatching                      true
% 2.56/1.00  --inst_eager_unprocessed_to_passive     true
% 2.56/1.00  --inst_prop_sim_given                   true
% 2.56/1.00  --inst_prop_sim_new                     false
% 2.56/1.00  --inst_subs_new                         false
% 2.56/1.00  --inst_eq_res_simp                      false
% 2.56/1.00  --inst_subs_given                       false
% 2.56/1.00  --inst_orphan_elimination               true
% 2.56/1.00  --inst_learning_loop_flag               true
% 2.56/1.00  --inst_learning_start                   3000
% 2.56/1.00  --inst_learning_factor                  2
% 2.56/1.00  --inst_start_prop_sim_after_learn       3
% 2.56/1.00  --inst_sel_renew                        solver
% 2.56/1.00  --inst_lit_activity_flag                true
% 2.56/1.00  --inst_restr_to_given                   false
% 2.56/1.00  --inst_activity_threshold               500
% 2.56/1.00  --inst_out_proof                        true
% 2.56/1.00  
% 2.56/1.00  ------ Resolution Options
% 2.56/1.00  
% 2.56/1.00  --resolution_flag                       false
% 2.56/1.00  --res_lit_sel                           adaptive
% 2.56/1.00  --res_lit_sel_side                      none
% 2.56/1.00  --res_ordering                          kbo
% 2.56/1.00  --res_to_prop_solver                    active
% 2.56/1.00  --res_prop_simpl_new                    false
% 2.56/1.00  --res_prop_simpl_given                  true
% 2.56/1.00  --res_passive_queue_type                priority_queues
% 2.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.00  --res_passive_queues_freq               [15;5]
% 2.56/1.00  --res_forward_subs                      full
% 2.56/1.00  --res_backward_subs                     full
% 2.56/1.00  --res_forward_subs_resolution           true
% 2.56/1.00  --res_backward_subs_resolution          true
% 2.56/1.00  --res_orphan_elimination                true
% 2.56/1.00  --res_time_limit                        2.
% 2.56/1.00  --res_out_proof                         true
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Options
% 2.56/1.00  
% 2.56/1.00  --superposition_flag                    true
% 2.56/1.00  --sup_passive_queue_type                priority_queues
% 2.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.00  --demod_completeness_check              fast
% 2.56/1.00  --demod_use_ground                      true
% 2.56/1.00  --sup_to_prop_solver                    passive
% 2.56/1.00  --sup_prop_simpl_new                    true
% 2.56/1.00  --sup_prop_simpl_given                  true
% 2.56/1.00  --sup_fun_splitting                     false
% 2.56/1.00  --sup_smt_interval                      50000
% 2.56/1.00  
% 2.56/1.00  ------ Superposition Simplification Setup
% 2.56/1.00  
% 2.56/1.00  --sup_indices_passive                   []
% 2.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_full_bw                           [BwDemod]
% 2.56/1.00  --sup_immed_triv                        [TrivRules]
% 2.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_immed_bw_main                     []
% 2.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.00  
% 2.56/1.00  ------ Combination Options
% 2.56/1.00  
% 2.56/1.00  --comb_res_mult                         3
% 2.56/1.00  --comb_sup_mult                         2
% 2.56/1.00  --comb_inst_mult                        10
% 2.56/1.00  
% 2.56/1.00  ------ Debug Options
% 2.56/1.00  
% 2.56/1.00  --dbg_backtrace                         false
% 2.56/1.00  --dbg_dump_prop_clauses                 false
% 2.56/1.00  --dbg_dump_prop_clauses_file            -
% 2.56/1.00  --dbg_out_stat                          false
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  ------ Proving...
% 2.56/1.00  
% 2.56/1.00  
% 2.56/1.00  % SZS status Theorem for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.00  
% 2.56/1.00  fof(f11,conjecture,(
% 2.56/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f12,negated_conjecture,(
% 2.56/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.56/1.00    inference(negated_conjecture,[],[f11])).
% 2.56/1.00  
% 2.56/1.00  fof(f21,plain,(
% 2.56/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.56/1.00    inference(ennf_transformation,[],[f12])).
% 2.56/1.00  
% 2.56/1.00  fof(f22,plain,(
% 2.56/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.56/1.00    inference(flattening,[],[f21])).
% 2.56/1.00  
% 2.56/1.00  fof(f33,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f32,plain,(
% 2.56/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f34,plain,(
% 2.56/1.00    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f33,f32])).
% 2.56/1.00  
% 2.56/1.00  fof(f62,plain,(
% 2.56/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f4,axiom,(
% 2.56/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f27,plain,(
% 2.56/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.56/1.00    inference(nnf_transformation,[],[f4])).
% 2.56/1.00  
% 2.56/1.00  fof(f42,plain,(
% 2.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f27])).
% 2.56/1.00  
% 2.56/1.00  fof(f5,axiom,(
% 2.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f13,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(ennf_transformation,[],[f5])).
% 2.56/1.00  
% 2.56/1.00  fof(f44,plain,(
% 2.56/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f13])).
% 2.56/1.00  
% 2.56/1.00  fof(f43,plain,(
% 2.56/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f27])).
% 2.56/1.00  
% 2.56/1.00  fof(f6,axiom,(
% 2.56/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f45,plain,(
% 2.56/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f6])).
% 2.56/1.00  
% 2.56/1.00  fof(f10,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f19,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f10])).
% 2.56/1.00  
% 2.56/1.00  fof(f20,plain,(
% 2.56/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(flattening,[],[f19])).
% 2.56/1.00  
% 2.56/1.00  fof(f31,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(nnf_transformation,[],[f20])).
% 2.56/1.00  
% 2.56/1.00  fof(f51,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f31])).
% 2.56/1.00  
% 2.56/1.00  fof(f58,plain,(
% 2.56/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f59,plain,(
% 2.56/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f8,axiom,(
% 2.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f16,plain,(
% 2.56/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(ennf_transformation,[],[f8])).
% 2.56/1.00  
% 2.56/1.00  fof(f48,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f16])).
% 2.56/1.00  
% 2.56/1.00  fof(f61,plain,(
% 2.56/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f7,axiom,(
% 2.56/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f14,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/1.00    inference(ennf_transformation,[],[f7])).
% 2.56/1.00  
% 2.56/1.00  fof(f15,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(flattening,[],[f14])).
% 2.56/1.00  
% 2.56/1.00  fof(f28,plain,(
% 2.56/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.56/1.00    introduced(choice_axiom,[])).
% 2.56/1.00  
% 2.56/1.00  fof(f29,plain,(
% 2.56/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).
% 2.56/1.00  
% 2.56/1.00  fof(f46,plain,(
% 2.56/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f29])).
% 2.56/1.00  
% 2.56/1.00  fof(f60,plain,(
% 2.56/1.00    v1_funct_1(sK4)),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f57,plain,(
% 2.56/1.00    v1_funct_1(sK3)),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f63,plain,(
% 2.56/1.00    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f47,plain,(
% 2.56/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f29])).
% 2.56/1.00  
% 2.56/1.00  fof(f9,axiom,(
% 2.56/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f17,plain,(
% 2.56/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.56/1.00    inference(ennf_transformation,[],[f9])).
% 2.56/1.00  
% 2.56/1.00  fof(f18,plain,(
% 2.56/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(flattening,[],[f17])).
% 2.56/1.00  
% 2.56/1.00  fof(f30,plain,(
% 2.56/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.00    inference(nnf_transformation,[],[f18])).
% 2.56/1.00  
% 2.56/1.00  fof(f50,plain,(
% 2.56/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f30])).
% 2.56/1.00  
% 2.56/1.00  fof(f69,plain,(
% 2.56/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(equality_resolution,[],[f50])).
% 2.56/1.00  
% 2.56/1.00  fof(f64,plain,(
% 2.56/1.00    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.56/1.00    inference(cnf_transformation,[],[f34])).
% 2.56/1.00  
% 2.56/1.00  fof(f3,axiom,(
% 2.56/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f25,plain,(
% 2.56/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.56/1.00    inference(nnf_transformation,[],[f3])).
% 2.56/1.00  
% 2.56/1.00  fof(f26,plain,(
% 2.56/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.56/1.00    inference(flattening,[],[f25])).
% 2.56/1.00  
% 2.56/1.00  fof(f41,plain,(
% 2.56/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.56/1.00    inference(cnf_transformation,[],[f26])).
% 2.56/1.00  
% 2.56/1.00  fof(f67,plain,(
% 2.56/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.56/1.00    inference(equality_resolution,[],[f41])).
% 2.56/1.00  
% 2.56/1.00  fof(f55,plain,(
% 2.56/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.00    inference(cnf_transformation,[],[f31])).
% 2.56/1.00  
% 2.56/1.00  fof(f72,plain,(
% 2.56/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.56/1.00    inference(equality_resolution,[],[f55])).
% 2.56/1.00  
% 2.56/1.00  fof(f1,axiom,(
% 2.56/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f23,plain,(
% 2.56/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/1.00    inference(nnf_transformation,[],[f1])).
% 2.56/1.00  
% 2.56/1.00  fof(f24,plain,(
% 2.56/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/1.00    inference(flattening,[],[f23])).
% 2.56/1.00  
% 2.56/1.00  fof(f37,plain,(
% 2.56/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f24])).
% 2.56/1.00  
% 2.56/1.00  fof(f2,axiom,(
% 2.56/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.56/1.00  
% 2.56/1.00  fof(f38,plain,(
% 2.56/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.56/1.00    inference(cnf_transformation,[],[f2])).
% 2.56/1.00  
% 2.56/1.00  cnf(c_24,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2293,plain,
% 2.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_8,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2299,plain,
% 2.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.56/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3866,plain,
% 2.56/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2293,c_2299]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_9,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/1.00      | ~ v1_relat_1(X1)
% 2.56/1.00      | v1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_7,plain,
% 2.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_207,plain,
% 2.56/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.56/1.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_208,plain,
% 2.56/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_207]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_265,plain,
% 2.56/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.56/1.00      inference(bin_hyper_res,[status(thm)],[c_9,c_208]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2289,plain,
% 2.56/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.56/1.00      | v1_relat_1(X1) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5030,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_3866,c_2289]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_10,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.56/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2298,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5127,plain,
% 2.56/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 2.56/1.00      inference(forward_subsumption_resolution,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_5030,c_2298]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_21,plain,
% 2.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.56/1.00      | k1_xboole_0 = X2 ),
% 2.56/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_28,negated_conjecture,
% 2.56/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.56/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_914,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.56/1.00      | sK3 != X0
% 2.56/1.00      | sK2 != X2
% 2.56/1.00      | sK1 != X1
% 2.56/1.00      | k1_xboole_0 = X2 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_915,plain,
% 2.56/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.56/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.56/1.00      | k1_xboole_0 = sK2 ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_914]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_27,negated_conjecture,
% 2.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.56/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_917,plain,
% 2.56/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_915,c_27]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2291,plain,
% 2.56/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_13,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2295,plain,
% 2.56/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.56/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2640,plain,
% 2.56/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2291,c_2295]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2906,plain,
% 2.56/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_917,c_2640]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_25,negated_conjecture,
% 2.56/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.56/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_903,plain,
% 2.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.56/1.00      | sK4 != X0
% 2.56/1.00      | sK2 != X2
% 2.56/1.00      | sK1 != X1
% 2.56/1.00      | k1_xboole_0 = X2 ),
% 2.56/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_904,plain,
% 2.56/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.56/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.56/1.00      | k1_xboole_0 = sK2 ),
% 2.56/1.00      inference(unflattening,[status(thm)],[c_903]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_906,plain,
% 2.56/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_904,c_24]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2639,plain,
% 2.56/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2293,c_2295]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2850,plain,
% 2.56/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_906,c_2639]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_12,plain,
% 2.56/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.56/1.00      | ~ v1_funct_1(X1)
% 2.56/1.00      | ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | ~ v1_relat_1(X1)
% 2.56/1.00      | X1 = X0
% 2.56/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2296,plain,
% 2.56/1.00      ( X0 = X1
% 2.56/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.56/1.00      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_funct_1(X1) != iProver_top
% 2.56/1.00      | v1_relat_1(X1) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3090,plain,
% 2.56/1.00      ( k1_relat_1(X0) != sK1
% 2.56/1.00      | sK4 = X0
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2850,c_2296]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_26,negated_conjecture,
% 2.56/1.00      ( v1_funct_1(sK4) ),
% 2.56/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_33,plain,
% 2.56/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3278,plain,
% 2.56/1.00      ( v1_funct_1(X0) != iProver_top
% 2.56/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | sK4 = X0
% 2.56/1.00      | k1_relat_1(X0) != sK1
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3090,c_33]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3279,plain,
% 2.56/1.00      ( k1_relat_1(X0) != sK1
% 2.56/1.00      | sK4 = X0
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_3278]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3292,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 2.56/1.00      | v1_funct_1(sK3) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2906,c_3279]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_29,negated_conjecture,
% 2.56/1.00      ( v1_funct_1(sK3) ),
% 2.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_30,plain,
% 2.56/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3339,plain,
% 2.56/1.00      ( r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3292,c_30]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3340,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_3339]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3348,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2906,c_3340]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_23,negated_conjecture,
% 2.56/1.00      ( ~ r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.56/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2294,plain,
% 2.56/1.00      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.56/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3356,plain,
% 2.56/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_3348,c_2294]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5130,plain,
% 2.56/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_5127,c_3356]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3091,plain,
% 2.56/1.00      ( k1_relat_1(X0) != sK1
% 2.56/1.00      | sK3 = X0
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_funct_1(sK3) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2906,c_2296]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3421,plain,
% 2.56/1.00      ( v1_funct_1(X0) != iProver_top
% 2.56/1.00      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | sK3 = X0
% 2.56/1.00      | k1_relat_1(X0) != sK1
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3091,c_30]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3422,plain,
% 2.56/1.00      ( k1_relat_1(X0) != sK1
% 2.56/1.00      | sK3 = X0
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(X0,sK3),k1_relat_1(X0)) = iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_3421]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3434,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2850,c_3422]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3620,plain,
% 2.56/1.00      ( r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_3434,c_33]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3621,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_3620]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3629,plain,
% 2.56/1.00      ( sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | r2_hidden(sK0(sK4,sK3),sK1) = iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2850,c_3621]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3637,plain,
% 2.56/1.00      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_3629,c_2294]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5129,plain,
% 2.56/1.00      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_5127,c_3637]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3638,plain,
% 2.56/1.00      ( ~ v1_relat_1(sK4)
% 2.56/1.00      | ~ v1_relat_1(sK3)
% 2.56/1.00      | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0 ),
% 2.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3637]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5128,plain,
% 2.56/1.00      ( v1_relat_1(sK4) ),
% 2.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5127]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_3867,plain,
% 2.56/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_2291,c_2299]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5031,plain,
% 2.56/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.56/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.56/1.00      inference(superposition,[status(thm)],[c_3867,c_2289]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5152,plain,
% 2.56/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.56/1.00      inference(forward_subsumption_resolution,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_5031,c_2298]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5153,plain,
% 2.56/1.00      ( v1_relat_1(sK3) ),
% 2.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5152]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5278,plain,
% 2.56/1.00      ( sK2 = k1_xboole_0
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3)) ),
% 2.56/1.00      inference(global_propositional_subsumption,
% 2.56/1.00                [status(thm)],
% 2.56/1.00                [c_5129,c_3638,c_5128,c_5153]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5279,plain,
% 2.56/1.00      ( k1_funct_1(sK4,sK0(sK4,sK3)) = k1_funct_1(sK3,sK0(sK4,sK3))
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0 ),
% 2.56/1.00      inference(renaming,[status(thm)],[c_5278]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_11,plain,
% 2.56/1.00      ( ~ v1_funct_1(X0)
% 2.56/1.00      | ~ v1_funct_1(X1)
% 2.56/1.00      | ~ v1_relat_1(X1)
% 2.56/1.00      | ~ v1_relat_1(X0)
% 2.56/1.00      | X0 = X1
% 2.56/1.00      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.56/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.56/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_2297,plain,
% 2.56/1.00      ( X0 = X1
% 2.56/1.00      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.56/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.56/1.00      | v1_funct_1(X1) != iProver_top
% 2.56/1.00      | v1_funct_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(X0) != iProver_top
% 2.56/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.56/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.56/1.00  
% 2.56/1.00  cnf(c_5283,plain,
% 2.56/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.56/1.00      | sK4 = sK3
% 2.56/1.00      | sK2 = k1_xboole_0
% 2.56/1.00      | v1_funct_1(sK4) != iProver_top
% 2.56/1.00      | v1_funct_1(sK3) != iProver_top
% 2.56/1.00      | v1_relat_1(sK4) != iProver_top
% 2.56/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_5279,c_2297]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5284,plain,
% 2.56/1.01      ( ~ v1_funct_1(sK4)
% 2.56/1.01      | ~ v1_funct_1(sK3)
% 2.56/1.01      | ~ v1_relat_1(sK4)
% 2.56/1.01      | ~ v1_relat_1(sK3)
% 2.56/1.01      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.56/1.01      | sK4 = sK3
% 2.56/1.01      | sK2 = k1_xboole_0 ),
% 2.56/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5283]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5286,plain,
% 2.56/1.01      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.56/1.01      | sK4 = sK3
% 2.56/1.01      | sK2 = k1_xboole_0 ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_5283,c_29,c_26,c_5128,c_5153,c_5284]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5291,plain,
% 2.56/1.01      ( k1_relat_1(sK3) != sK1 | sK4 = sK3 | sK2 = k1_xboole_0 ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_2850,c_5286]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5376,plain,
% 2.56/1.01      ( sK2 = k1_xboole_0 | sK4 = sK3 ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_5130,c_2906,c_5291]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5377,plain,
% 2.56/1.01      ( sK4 = sK3 | sK2 = k1_xboole_0 ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_5376]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_14,plain,
% 2.56/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.56/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_22,negated_conjecture,
% 2.56/1.01      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 2.56/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_360,plain,
% 2.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.01      | sK4 != X0
% 2.56/1.01      | sK3 != X0
% 2.56/1.01      | sK2 != X2
% 2.56/1.01      | sK1 != X1 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_361,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.56/1.01      | sK3 != sK4 ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_360]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_363,plain,
% 2.56/1.01      ( sK3 != sK4 ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_361,c_24]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5394,plain,
% 2.56/1.01      ( sK2 = k1_xboole_0 ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_5377,c_363]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5416,plain,
% 2.56/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5394,c_2293]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4,plain,
% 2.56/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.56/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5422,plain,
% 2.56/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5416,c_4]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5417,plain,
% 2.56/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5394,c_2291]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5419,plain,
% 2.56/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5417,c_4]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_17,plain,
% 2.56/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.56/1.01      | k1_xboole_0 = X1
% 2.56/1.01      | k1_xboole_0 = X0 ),
% 2.56/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_841,plain,
% 2.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.56/1.01      | sK4 != X0
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | sK1 != X1
% 2.56/1.01      | k1_xboole_0 = X1
% 2.56/1.01      | k1_xboole_0 = X0 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_842,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | k1_xboole_0 = sK4
% 2.56/1.01      | k1_xboole_0 = sK1 ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_841]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2288,plain,
% 2.56/1.01      ( sK2 != k1_xboole_0
% 2.56/1.01      | k1_xboole_0 = sK4
% 2.56/1.01      | k1_xboole_0 = sK1
% 2.56/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2389,plain,
% 2.56/1.01      ( sK4 = k1_xboole_0
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | sK1 = k1_xboole_0
% 2.56/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_2288,c_4]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_0,plain,
% 2.56/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.56/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2661,plain,
% 2.56/1.01      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2662,plain,
% 2.56/1.01      ( sK4 = X0
% 2.56/1.01      | r1_tarski(X0,sK4) != iProver_top
% 2.56/1.01      | r1_tarski(sK4,X0) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2664,plain,
% 2.56/1.01      ( sK4 = k1_xboole_0
% 2.56/1.01      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.56/1.01      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2662]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3,plain,
% 2.56/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2780,plain,
% 2.56/1.01      ( r1_tarski(k1_xboole_0,sK4) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2783,plain,
% 2.56/1.01      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2780]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2997,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2998,plain,
% 2.56/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.56/1.01      | r1_tarski(sK4,X0) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3000,plain,
% 2.56/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.56/1.01      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2998]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3076,plain,
% 2.56/1.01      ( sK4 = k1_xboole_0
% 2.56/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_2389,c_2664,c_2783,c_3000]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_857,plain,
% 2.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.56/1.01      | sK3 != X0
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | sK1 != X1
% 2.56/1.01      | k1_xboole_0 = X1
% 2.56/1.01      | k1_xboole_0 = X0 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_858,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | k1_xboole_0 = sK3
% 2.56/1.01      | k1_xboole_0 = sK1 ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_857]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2287,plain,
% 2.56/1.01      ( sK2 != k1_xboole_0
% 2.56/1.01      | k1_xboole_0 = sK3
% 2.56/1.01      | k1_xboole_0 = sK1
% 2.56/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2380,plain,
% 2.56/1.01      ( sK3 = k1_xboole_0
% 2.56/1.01      | sK2 != k1_xboole_0
% 2.56/1.01      | sK1 = k1_xboole_0
% 2.56/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_2287,c_4]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2808,plain,
% 2.56/1.01      ( r1_tarski(k1_xboole_0,sK3) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2811,plain,
% 2.56/1.01      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2822,plain,
% 2.56/1.01      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2823,plain,
% 2.56/1.01      ( sK3 = X0
% 2.56/1.01      | r1_tarski(X0,sK3) != iProver_top
% 2.56/1.01      | r1_tarski(sK3,X0) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2825,plain,
% 2.56/1.01      ( sK3 = k1_xboole_0
% 2.56/1.01      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 2.56/1.01      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2823]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3013,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3014,plain,
% 2.56/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.56/1.01      | r1_tarski(sK3,X0) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3016,plain,
% 2.56/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.56/1.01      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_3014]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3032,plain,
% 2.56/1.01      ( sK3 = k1_xboole_0
% 2.56/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_2380,c_2811,c_2825,c_3016]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1778,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2500,plain,
% 2.56/1.01      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_1778]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2501,plain,
% 2.56/1.01      ( sK4 != k1_xboole_0 | sK3 = sK4 | sK3 != k1_xboole_0 ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2500]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(contradiction,plain,
% 2.56/1.01      ( $false ),
% 2.56/1.01      inference(minisat,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_5422,c_5419,c_3076,c_3032,c_2501,c_361,c_24]) ).
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.01  
% 2.56/1.01  ------                               Statistics
% 2.56/1.01  
% 2.56/1.01  ------ General
% 2.56/1.01  
% 2.56/1.01  abstr_ref_over_cycles:                  0
% 2.56/1.01  abstr_ref_under_cycles:                 0
% 2.56/1.01  gc_basic_clause_elim:                   0
% 2.56/1.01  forced_gc_time:                         0
% 2.56/1.01  parsing_time:                           0.009
% 2.56/1.01  unif_index_cands_time:                  0.
% 2.56/1.01  unif_index_add_time:                    0.
% 2.56/1.01  orderings_time:                         0.
% 2.56/1.01  out_proof_time:                         0.012
% 2.56/1.01  total_time:                             0.166
% 2.56/1.01  num_of_symbols:                         49
% 2.56/1.01  num_of_terms:                           3757
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing
% 2.56/1.01  
% 2.56/1.01  num_of_splits:                          0
% 2.56/1.01  num_of_split_atoms:                     0
% 2.56/1.01  num_of_reused_defs:                     0
% 2.56/1.01  num_eq_ax_congr_red:                    14
% 2.56/1.01  num_of_sem_filtered_clauses:            1
% 2.56/1.01  num_of_subtypes:                        0
% 2.56/1.01  monotx_restored_types:                  0
% 2.56/1.01  sat_num_of_epr_types:                   0
% 2.56/1.01  sat_num_of_non_cyclic_types:            0
% 2.56/1.01  sat_guarded_non_collapsed_types:        0
% 2.56/1.01  num_pure_diseq_elim:                    0
% 2.56/1.01  simp_replaced_by:                       0
% 2.56/1.01  res_preprocessed:                       127
% 2.56/1.01  prep_upred:                             0
% 2.56/1.01  prep_unflattend:                        82
% 2.56/1.01  smt_new_axioms:                         0
% 2.56/1.01  pred_elim_cands:                        5
% 2.56/1.01  pred_elim:                              2
% 2.56/1.01  pred_elim_cl:                           4
% 2.56/1.01  pred_elim_cycles:                       7
% 2.56/1.01  merged_defs:                            8
% 2.56/1.01  merged_defs_ncl:                        0
% 2.56/1.01  bin_hyper_res:                          9
% 2.56/1.01  prep_cycles:                            4
% 2.56/1.01  pred_elim_time:                         0.015
% 2.56/1.01  splitting_time:                         0.
% 2.56/1.01  sem_filter_time:                        0.
% 2.56/1.01  monotx_time:                            0.
% 2.56/1.01  subtype_inf_time:                       0.
% 2.56/1.01  
% 2.56/1.01  ------ Problem properties
% 2.56/1.01  
% 2.56/1.01  clauses:                                25
% 2.56/1.01  conjectures:                            5
% 2.56/1.01  epr:                                    7
% 2.56/1.01  horn:                                   19
% 2.56/1.01  ground:                                 11
% 2.56/1.01  unary:                                  10
% 2.56/1.01  binary:                                 6
% 2.56/1.01  lits:                                   59
% 2.56/1.01  lits_eq:                                28
% 2.56/1.01  fd_pure:                                0
% 2.56/1.01  fd_pseudo:                              0
% 2.56/1.01  fd_cond:                                1
% 2.56/1.01  fd_pseudo_cond:                         3
% 2.56/1.01  ac_symbols:                             0
% 2.56/1.01  
% 2.56/1.01  ------ Propositional Solver
% 2.56/1.01  
% 2.56/1.01  prop_solver_calls:                      28
% 2.56/1.01  prop_fast_solver_calls:                 1112
% 2.56/1.01  smt_solver_calls:                       0
% 2.56/1.01  smt_fast_solver_calls:                  0
% 2.56/1.01  prop_num_of_clauses:                    1500
% 2.56/1.01  prop_preprocess_simplified:             4831
% 2.56/1.01  prop_fo_subsumed:                       20
% 2.56/1.01  prop_solver_time:                       0.
% 2.56/1.01  smt_solver_time:                        0.
% 2.56/1.01  smt_fast_solver_time:                   0.
% 2.56/1.01  prop_fast_solver_time:                  0.
% 2.56/1.01  prop_unsat_core_time:                   0.
% 2.56/1.01  
% 2.56/1.01  ------ QBF
% 2.56/1.01  
% 2.56/1.01  qbf_q_res:                              0
% 2.56/1.01  qbf_num_tautologies:                    0
% 2.56/1.01  qbf_prep_cycles:                        0
% 2.56/1.01  
% 2.56/1.01  ------ BMC1
% 2.56/1.01  
% 2.56/1.01  bmc1_current_bound:                     -1
% 2.56/1.01  bmc1_last_solved_bound:                 -1
% 2.56/1.01  bmc1_unsat_core_size:                   -1
% 2.56/1.01  bmc1_unsat_core_parents_size:           -1
% 2.56/1.01  bmc1_merge_next_fun:                    0
% 2.56/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.01  
% 2.56/1.01  ------ Instantiation
% 2.56/1.01  
% 2.56/1.01  inst_num_of_clauses:                    480
% 2.56/1.01  inst_num_in_passive:                    28
% 2.56/1.01  inst_num_in_active:                     284
% 2.56/1.01  inst_num_in_unprocessed:                170
% 2.56/1.01  inst_num_of_loops:                      310
% 2.56/1.01  inst_num_of_learning_restarts:          0
% 2.56/1.01  inst_num_moves_active_passive:          23
% 2.56/1.01  inst_lit_activity:                      0
% 2.56/1.01  inst_lit_activity_moves:                0
% 2.56/1.01  inst_num_tautologies:                   0
% 2.56/1.01  inst_num_prop_implied:                  0
% 2.56/1.01  inst_num_existing_simplified:           0
% 2.56/1.01  inst_num_eq_res_simplified:             0
% 2.56/1.01  inst_num_child_elim:                    0
% 2.56/1.01  inst_num_of_dismatching_blockings:      112
% 2.56/1.01  inst_num_of_non_proper_insts:           629
% 2.56/1.01  inst_num_of_duplicates:                 0
% 2.56/1.01  inst_inst_num_from_inst_to_res:         0
% 2.56/1.01  inst_dismatching_checking_time:         0.
% 2.56/1.01  
% 2.56/1.01  ------ Resolution
% 2.56/1.01  
% 2.56/1.01  res_num_of_clauses:                     0
% 2.56/1.01  res_num_in_passive:                     0
% 2.56/1.01  res_num_in_active:                      0
% 2.56/1.01  res_num_of_loops:                       131
% 2.56/1.01  res_forward_subset_subsumed:            28
% 2.56/1.01  res_backward_subset_subsumed:           4
% 2.56/1.01  res_forward_subsumed:                   2
% 2.56/1.01  res_backward_subsumed:                  0
% 2.56/1.01  res_forward_subsumption_resolution:     1
% 2.56/1.01  res_backward_subsumption_resolution:    0
% 2.56/1.01  res_clause_to_clause_subsumption:       251
% 2.56/1.01  res_orphan_elimination:                 0
% 2.56/1.01  res_tautology_del:                      90
% 2.56/1.01  res_num_eq_res_simplified:              0
% 2.56/1.01  res_num_sel_changes:                    0
% 2.56/1.01  res_moves_from_active_to_pass:          0
% 2.56/1.01  
% 2.56/1.01  ------ Superposition
% 2.56/1.01  
% 2.56/1.01  sup_time_total:                         0.
% 2.56/1.01  sup_time_generating:                    0.
% 2.56/1.01  sup_time_sim_full:                      0.
% 2.56/1.01  sup_time_sim_immed:                     0.
% 2.56/1.01  
% 2.56/1.01  sup_num_of_clauses:                     46
% 2.56/1.01  sup_num_in_active:                      37
% 2.56/1.01  sup_num_in_passive:                     9
% 2.56/1.01  sup_num_of_loops:                       61
% 2.56/1.01  sup_fw_superposition:                   49
% 2.56/1.01  sup_bw_superposition:                   28
% 2.56/1.01  sup_immediate_simplified:               23
% 2.56/1.01  sup_given_eliminated:                   1
% 2.56/1.01  comparisons_done:                       0
% 2.56/1.01  comparisons_avoided:                    39
% 2.56/1.01  
% 2.56/1.01  ------ Simplifications
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  sim_fw_subset_subsumed:                 11
% 2.56/1.01  sim_bw_subset_subsumed:                 5
% 2.56/1.01  sim_fw_subsumed:                        2
% 2.56/1.01  sim_bw_subsumed:                        1
% 2.56/1.01  sim_fw_subsumption_res:                 4
% 2.56/1.01  sim_bw_subsumption_res:                 0
% 2.56/1.01  sim_tautology_del:                      2
% 2.56/1.01  sim_eq_tautology_del:                   19
% 2.56/1.01  sim_eq_res_simp:                        0
% 2.56/1.01  sim_fw_demodulated:                     10
% 2.56/1.01  sim_bw_demodulated:                     18
% 2.56/1.01  sim_light_normalised:                   2
% 2.56/1.01  sim_joinable_taut:                      0
% 2.56/1.01  sim_joinable_simp:                      0
% 2.56/1.01  sim_ac_normalised:                      0
% 2.56/1.01  sim_smt_subsumption:                    0
% 2.56/1.01  
%------------------------------------------------------------------------------
