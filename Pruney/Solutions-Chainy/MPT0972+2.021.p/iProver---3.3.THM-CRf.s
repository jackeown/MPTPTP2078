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
% DateTime   : Thu Dec  3 12:01:12 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  162 (1503 expanded)
%              Number of clauses        :   97 ( 451 expanded)
%              Number of leaves         :   18 ( 372 expanded)
%              Depth                    :   25
%              Number of atoms          :  539 (9604 expanded)
%              Number of equality atoms :  264 (2278 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f45,f44])).

fof(f77,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f80,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_433,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_435,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_28])).

cnf(c_1007,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1009,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1867,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1007,c_1009])).

cnf(c_2007,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_435,c_1867])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_446,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_31])).

cnf(c_1005,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1868,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1005,c_1009])).

cnf(c_2144,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_446,c_1868])).

cnf(c_15,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1011,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2461,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_1011])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1218,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_2750,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2461,c_37,c_39,c_1218])).

cnf(c_2751,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2750])).

cnf(c_2763,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_2751])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_350,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1221,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_624,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1362,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_625,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1246,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1660,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2824,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2763,c_34,c_36,c_28,c_350,c_1221,c_1362,c_1660])).

cnf(c_2830,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_2824])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1008,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2850,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2830,c_1008])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1012,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3083,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1012])).

cnf(c_3099,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3083])).

cnf(c_4154,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3083,c_33,c_31,c_30,c_28,c_350,c_1217,c_1220,c_1362,c_1660,c_3099])).

cnf(c_4158,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2007,c_4154])).

cnf(c_4159,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4158,c_2144])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1019,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3240,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_1015])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1020,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3446,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_1020])).

cnf(c_3583,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_3446])).

cnf(c_4165,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4159,c_3583])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4272,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4165,c_8])).

cnf(c_3239,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1015])).

cnf(c_3425,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_1020])).

cnf(c_3542,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_3425])).

cnf(c_4166,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4159,c_3542])).

cnf(c_4269,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4166,c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_3195,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_3198,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3195])).

cnf(c_2911,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_2914,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1594,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1595,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_1597,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_1565,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK0(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1571,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK0(X0,sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_1573,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_1554,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK0(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1560,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK0(X0,sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1554])).

cnf(c_1562,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_1453,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1454,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_1456,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1247,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4272,c_4269,c_3198,c_2914,c_1597,c_1573,c_1562,c_1456,c_1247,c_350,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.75/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/0.99  
% 2.75/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.75/0.99  
% 2.75/0.99  ------  iProver source info
% 2.75/0.99  
% 2.75/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.75/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.75/0.99  git: non_committed_changes: false
% 2.75/0.99  git: last_make_outside_of_git: false
% 2.75/0.99  
% 2.75/0.99  ------ 
% 2.75/0.99  
% 2.75/0.99  ------ Input Options
% 2.75/0.99  
% 2.75/0.99  --out_options                           all
% 2.75/0.99  --tptp_safe_out                         true
% 2.75/0.99  --problem_path                          ""
% 2.75/0.99  --include_path                          ""
% 2.75/0.99  --clausifier                            res/vclausify_rel
% 2.75/0.99  --clausifier_options                    --mode clausify
% 2.75/0.99  --stdin                                 false
% 2.75/0.99  --stats_out                             all
% 2.75/0.99  
% 2.75/0.99  ------ General Options
% 2.75/0.99  
% 2.75/0.99  --fof                                   false
% 2.75/0.99  --time_out_real                         305.
% 2.75/0.99  --time_out_virtual                      -1.
% 2.75/0.99  --symbol_type_check                     false
% 2.75/0.99  --clausify_out                          false
% 2.75/0.99  --sig_cnt_out                           false
% 2.75/0.99  --trig_cnt_out                          false
% 2.75/0.99  --trig_cnt_out_tolerance                1.
% 2.75/0.99  --trig_cnt_out_sk_spl                   false
% 2.75/0.99  --abstr_cl_out                          false
% 2.75/0.99  
% 2.75/0.99  ------ Global Options
% 2.75/0.99  
% 2.75/0.99  --schedule                              default
% 2.75/0.99  --add_important_lit                     false
% 2.75/0.99  --prop_solver_per_cl                    1000
% 2.75/0.99  --min_unsat_core                        false
% 2.75/0.99  --soft_assumptions                      false
% 2.75/0.99  --soft_lemma_size                       3
% 2.75/0.99  --prop_impl_unit_size                   0
% 2.75/0.99  --prop_impl_unit                        []
% 2.75/0.99  --share_sel_clauses                     true
% 2.75/0.99  --reset_solvers                         false
% 2.75/0.99  --bc_imp_inh                            [conj_cone]
% 2.75/0.99  --conj_cone_tolerance                   3.
% 2.75/0.99  --extra_neg_conj                        none
% 2.75/0.99  --large_theory_mode                     true
% 2.75/0.99  --prolific_symb_bound                   200
% 2.75/0.99  --lt_threshold                          2000
% 2.75/0.99  --clause_weak_htbl                      true
% 2.75/0.99  --gc_record_bc_elim                     false
% 2.75/0.99  
% 2.75/0.99  ------ Preprocessing Options
% 2.75/0.99  
% 2.75/0.99  --preprocessing_flag                    true
% 2.75/0.99  --time_out_prep_mult                    0.1
% 2.75/0.99  --splitting_mode                        input
% 2.75/0.99  --splitting_grd                         true
% 2.75/0.99  --splitting_cvd                         false
% 2.75/0.99  --splitting_cvd_svl                     false
% 2.75/0.99  --splitting_nvd                         32
% 2.75/0.99  --sub_typing                            true
% 2.75/0.99  --prep_gs_sim                           true
% 2.75/0.99  --prep_unflatten                        true
% 2.75/0.99  --prep_res_sim                          true
% 2.75/0.99  --prep_upred                            true
% 2.75/0.99  --prep_sem_filter                       exhaustive
% 2.75/0.99  --prep_sem_filter_out                   false
% 2.75/0.99  --pred_elim                             true
% 2.75/0.99  --res_sim_input                         true
% 2.75/0.99  --eq_ax_congr_red                       true
% 2.75/0.99  --pure_diseq_elim                       true
% 2.75/0.99  --brand_transform                       false
% 2.75/0.99  --non_eq_to_eq                          false
% 2.75/0.99  --prep_def_merge                        true
% 2.75/0.99  --prep_def_merge_prop_impl              false
% 2.75/0.99  --prep_def_merge_mbd                    true
% 2.75/0.99  --prep_def_merge_tr_red                 false
% 2.75/0.99  --prep_def_merge_tr_cl                  false
% 2.75/0.99  --smt_preprocessing                     true
% 2.75/0.99  --smt_ac_axioms                         fast
% 2.75/0.99  --preprocessed_out                      false
% 2.75/0.99  --preprocessed_stats                    false
% 2.75/0.99  
% 2.75/0.99  ------ Abstraction refinement Options
% 2.75/0.99  
% 2.75/0.99  --abstr_ref                             []
% 2.75/0.99  --abstr_ref_prep                        false
% 2.75/0.99  --abstr_ref_until_sat                   false
% 2.75/0.99  --abstr_ref_sig_restrict                funpre
% 2.75/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/0.99  --abstr_ref_under                       []
% 2.75/0.99  
% 2.75/0.99  ------ SAT Options
% 2.75/0.99  
% 2.75/0.99  --sat_mode                              false
% 2.75/0.99  --sat_fm_restart_options                ""
% 2.75/0.99  --sat_gr_def                            false
% 2.75/0.99  --sat_epr_types                         true
% 2.75/0.99  --sat_non_cyclic_types                  false
% 2.75/0.99  --sat_finite_models                     false
% 2.75/0.99  --sat_fm_lemmas                         false
% 2.75/0.99  --sat_fm_prep                           false
% 2.75/0.99  --sat_fm_uc_incr                        true
% 2.75/0.99  --sat_out_model                         small
% 2.75/0.99  --sat_out_clauses                       false
% 2.75/0.99  
% 2.75/0.99  ------ QBF Options
% 2.75/0.99  
% 2.75/0.99  --qbf_mode                              false
% 2.75/0.99  --qbf_elim_univ                         false
% 2.75/0.99  --qbf_dom_inst                          none
% 2.75/0.99  --qbf_dom_pre_inst                      false
% 2.75/0.99  --qbf_sk_in                             false
% 2.75/0.99  --qbf_pred_elim                         true
% 2.75/0.99  --qbf_split                             512
% 2.75/0.99  
% 2.75/0.99  ------ BMC1 Options
% 2.75/0.99  
% 2.75/0.99  --bmc1_incremental                      false
% 2.75/0.99  --bmc1_axioms                           reachable_all
% 2.75/0.99  --bmc1_min_bound                        0
% 2.75/0.99  --bmc1_max_bound                        -1
% 2.75/0.99  --bmc1_max_bound_default                -1
% 2.75/0.99  --bmc1_symbol_reachability              true
% 2.75/0.99  --bmc1_property_lemmas                  false
% 2.75/0.99  --bmc1_k_induction                      false
% 2.75/0.99  --bmc1_non_equiv_states                 false
% 2.75/0.99  --bmc1_deadlock                         false
% 2.75/0.99  --bmc1_ucm                              false
% 2.75/0.99  --bmc1_add_unsat_core                   none
% 2.75/0.99  --bmc1_unsat_core_children              false
% 2.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/0.99  --bmc1_out_stat                         full
% 2.75/0.99  --bmc1_ground_init                      false
% 2.75/0.99  --bmc1_pre_inst_next_state              false
% 2.75/0.99  --bmc1_pre_inst_state                   false
% 2.75/0.99  --bmc1_pre_inst_reach_state             false
% 2.75/0.99  --bmc1_out_unsat_core                   false
% 2.75/0.99  --bmc1_aig_witness_out                  false
% 2.75/0.99  --bmc1_verbose                          false
% 2.75/0.99  --bmc1_dump_clauses_tptp                false
% 2.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.75/0.99  --bmc1_dump_file                        -
% 2.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.75/0.99  --bmc1_ucm_extend_mode                  1
% 2.75/0.99  --bmc1_ucm_init_mode                    2
% 2.75/0.99  --bmc1_ucm_cone_mode                    none
% 2.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.75/0.99  --bmc1_ucm_relax_model                  4
% 2.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/0.99  --bmc1_ucm_layered_model                none
% 2.75/1.00  --bmc1_ucm_max_lemma_size               10
% 2.75/1.00  
% 2.75/1.00  ------ AIG Options
% 2.75/1.00  
% 2.75/1.00  --aig_mode                              false
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation Options
% 2.75/1.00  
% 2.75/1.00  --instantiation_flag                    true
% 2.75/1.00  --inst_sos_flag                         false
% 2.75/1.00  --inst_sos_phase                        true
% 2.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel_side                     num_symb
% 2.75/1.00  --inst_solver_per_active                1400
% 2.75/1.00  --inst_solver_calls_frac                1.
% 2.75/1.00  --inst_passive_queue_type               priority_queues
% 2.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/1.00  --inst_passive_queues_freq              [25;2]
% 2.75/1.00  --inst_dismatching                      true
% 2.75/1.00  --inst_eager_unprocessed_to_passive     true
% 2.75/1.00  --inst_prop_sim_given                   true
% 2.75/1.00  --inst_prop_sim_new                     false
% 2.75/1.00  --inst_subs_new                         false
% 2.75/1.00  --inst_eq_res_simp                      false
% 2.75/1.00  --inst_subs_given                       false
% 2.75/1.00  --inst_orphan_elimination               true
% 2.75/1.00  --inst_learning_loop_flag               true
% 2.75/1.00  --inst_learning_start                   3000
% 2.75/1.00  --inst_learning_factor                  2
% 2.75/1.00  --inst_start_prop_sim_after_learn       3
% 2.75/1.00  --inst_sel_renew                        solver
% 2.75/1.00  --inst_lit_activity_flag                true
% 2.75/1.00  --inst_restr_to_given                   false
% 2.75/1.00  --inst_activity_threshold               500
% 2.75/1.00  --inst_out_proof                        true
% 2.75/1.00  
% 2.75/1.00  ------ Resolution Options
% 2.75/1.00  
% 2.75/1.00  --resolution_flag                       true
% 2.75/1.00  --res_lit_sel                           adaptive
% 2.75/1.00  --res_lit_sel_side                      none
% 2.75/1.00  --res_ordering                          kbo
% 2.75/1.00  --res_to_prop_solver                    active
% 2.75/1.00  --res_prop_simpl_new                    false
% 2.75/1.00  --res_prop_simpl_given                  true
% 2.75/1.00  --res_passive_queue_type                priority_queues
% 2.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/1.00  --res_passive_queues_freq               [15;5]
% 2.75/1.00  --res_forward_subs                      full
% 2.75/1.00  --res_backward_subs                     full
% 2.75/1.00  --res_forward_subs_resolution           true
% 2.75/1.00  --res_backward_subs_resolution          true
% 2.75/1.00  --res_orphan_elimination                true
% 2.75/1.00  --res_time_limit                        2.
% 2.75/1.00  --res_out_proof                         true
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Options
% 2.75/1.00  
% 2.75/1.00  --superposition_flag                    true
% 2.75/1.00  --sup_passive_queue_type                priority_queues
% 2.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.75/1.00  --demod_completeness_check              fast
% 2.75/1.00  --demod_use_ground                      true
% 2.75/1.00  --sup_to_prop_solver                    passive
% 2.75/1.00  --sup_prop_simpl_new                    true
% 2.75/1.00  --sup_prop_simpl_given                  true
% 2.75/1.00  --sup_fun_splitting                     false
% 2.75/1.00  --sup_smt_interval                      50000
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Simplification Setup
% 2.75/1.00  
% 2.75/1.00  --sup_indices_passive                   []
% 2.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_full_bw                           [BwDemod]
% 2.75/1.00  --sup_immed_triv                        [TrivRules]
% 2.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_immed_bw_main                     []
% 2.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  
% 2.75/1.00  ------ Combination Options
% 2.75/1.00  
% 2.75/1.00  --comb_res_mult                         3
% 2.75/1.00  --comb_sup_mult                         2
% 2.75/1.00  --comb_inst_mult                        10
% 2.75/1.00  
% 2.75/1.00  ------ Debug Options
% 2.75/1.00  
% 2.75/1.00  --dbg_backtrace                         false
% 2.75/1.00  --dbg_dump_prop_clauses                 false
% 2.75/1.00  --dbg_dump_prop_clauses_file            -
% 2.75/1.00  --dbg_out_stat                          false
% 2.75/1.00  ------ Parsing...
% 2.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.75/1.00  ------ Proving...
% 2.75/1.00  ------ Problem Properties 
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  clauses                                 28
% 2.75/1.00  conjectures                             5
% 2.75/1.00  EPR                                     7
% 2.75/1.00  Horn                                    21
% 2.75/1.00  unary                                   10
% 2.75/1.00  binary                                  7
% 2.75/1.00  lits                                    67
% 2.75/1.00  lits eq                                 28
% 2.75/1.00  fd_pure                                 0
% 2.75/1.00  fd_pseudo                               0
% 2.75/1.00  fd_cond                                 1
% 2.75/1.00  fd_pseudo_cond                          3
% 2.75/1.00  AC symbols                              0
% 2.75/1.00  
% 2.75/1.00  ------ Schedule dynamic 5 is on 
% 2.75/1.00  
% 2.75/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ 
% 2.75/1.00  Current options:
% 2.75/1.00  ------ 
% 2.75/1.00  
% 2.75/1.00  ------ Input Options
% 2.75/1.00  
% 2.75/1.00  --out_options                           all
% 2.75/1.00  --tptp_safe_out                         true
% 2.75/1.00  --problem_path                          ""
% 2.75/1.00  --include_path                          ""
% 2.75/1.00  --clausifier                            res/vclausify_rel
% 2.75/1.00  --clausifier_options                    --mode clausify
% 2.75/1.00  --stdin                                 false
% 2.75/1.00  --stats_out                             all
% 2.75/1.00  
% 2.75/1.00  ------ General Options
% 2.75/1.00  
% 2.75/1.00  --fof                                   false
% 2.75/1.00  --time_out_real                         305.
% 2.75/1.00  --time_out_virtual                      -1.
% 2.75/1.00  --symbol_type_check                     false
% 2.75/1.00  --clausify_out                          false
% 2.75/1.00  --sig_cnt_out                           false
% 2.75/1.00  --trig_cnt_out                          false
% 2.75/1.00  --trig_cnt_out_tolerance                1.
% 2.75/1.00  --trig_cnt_out_sk_spl                   false
% 2.75/1.00  --abstr_cl_out                          false
% 2.75/1.00  
% 2.75/1.00  ------ Global Options
% 2.75/1.00  
% 2.75/1.00  --schedule                              default
% 2.75/1.00  --add_important_lit                     false
% 2.75/1.00  --prop_solver_per_cl                    1000
% 2.75/1.00  --min_unsat_core                        false
% 2.75/1.00  --soft_assumptions                      false
% 2.75/1.00  --soft_lemma_size                       3
% 2.75/1.00  --prop_impl_unit_size                   0
% 2.75/1.00  --prop_impl_unit                        []
% 2.75/1.00  --share_sel_clauses                     true
% 2.75/1.00  --reset_solvers                         false
% 2.75/1.00  --bc_imp_inh                            [conj_cone]
% 2.75/1.00  --conj_cone_tolerance                   3.
% 2.75/1.00  --extra_neg_conj                        none
% 2.75/1.00  --large_theory_mode                     true
% 2.75/1.00  --prolific_symb_bound                   200
% 2.75/1.00  --lt_threshold                          2000
% 2.75/1.00  --clause_weak_htbl                      true
% 2.75/1.00  --gc_record_bc_elim                     false
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing Options
% 2.75/1.00  
% 2.75/1.00  --preprocessing_flag                    true
% 2.75/1.00  --time_out_prep_mult                    0.1
% 2.75/1.00  --splitting_mode                        input
% 2.75/1.00  --splitting_grd                         true
% 2.75/1.00  --splitting_cvd                         false
% 2.75/1.00  --splitting_cvd_svl                     false
% 2.75/1.00  --splitting_nvd                         32
% 2.75/1.00  --sub_typing                            true
% 2.75/1.00  --prep_gs_sim                           true
% 2.75/1.00  --prep_unflatten                        true
% 2.75/1.00  --prep_res_sim                          true
% 2.75/1.00  --prep_upred                            true
% 2.75/1.00  --prep_sem_filter                       exhaustive
% 2.75/1.00  --prep_sem_filter_out                   false
% 2.75/1.00  --pred_elim                             true
% 2.75/1.00  --res_sim_input                         true
% 2.75/1.00  --eq_ax_congr_red                       true
% 2.75/1.00  --pure_diseq_elim                       true
% 2.75/1.00  --brand_transform                       false
% 2.75/1.00  --non_eq_to_eq                          false
% 2.75/1.00  --prep_def_merge                        true
% 2.75/1.00  --prep_def_merge_prop_impl              false
% 2.75/1.00  --prep_def_merge_mbd                    true
% 2.75/1.00  --prep_def_merge_tr_red                 false
% 2.75/1.00  --prep_def_merge_tr_cl                  false
% 2.75/1.00  --smt_preprocessing                     true
% 2.75/1.00  --smt_ac_axioms                         fast
% 2.75/1.00  --preprocessed_out                      false
% 2.75/1.00  --preprocessed_stats                    false
% 2.75/1.00  
% 2.75/1.00  ------ Abstraction refinement Options
% 2.75/1.00  
% 2.75/1.00  --abstr_ref                             []
% 2.75/1.00  --abstr_ref_prep                        false
% 2.75/1.00  --abstr_ref_until_sat                   false
% 2.75/1.00  --abstr_ref_sig_restrict                funpre
% 2.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/1.00  --abstr_ref_under                       []
% 2.75/1.00  
% 2.75/1.00  ------ SAT Options
% 2.75/1.00  
% 2.75/1.00  --sat_mode                              false
% 2.75/1.00  --sat_fm_restart_options                ""
% 2.75/1.00  --sat_gr_def                            false
% 2.75/1.00  --sat_epr_types                         true
% 2.75/1.00  --sat_non_cyclic_types                  false
% 2.75/1.00  --sat_finite_models                     false
% 2.75/1.00  --sat_fm_lemmas                         false
% 2.75/1.00  --sat_fm_prep                           false
% 2.75/1.00  --sat_fm_uc_incr                        true
% 2.75/1.00  --sat_out_model                         small
% 2.75/1.00  --sat_out_clauses                       false
% 2.75/1.00  
% 2.75/1.00  ------ QBF Options
% 2.75/1.00  
% 2.75/1.00  --qbf_mode                              false
% 2.75/1.00  --qbf_elim_univ                         false
% 2.75/1.00  --qbf_dom_inst                          none
% 2.75/1.00  --qbf_dom_pre_inst                      false
% 2.75/1.00  --qbf_sk_in                             false
% 2.75/1.00  --qbf_pred_elim                         true
% 2.75/1.00  --qbf_split                             512
% 2.75/1.00  
% 2.75/1.00  ------ BMC1 Options
% 2.75/1.00  
% 2.75/1.00  --bmc1_incremental                      false
% 2.75/1.00  --bmc1_axioms                           reachable_all
% 2.75/1.00  --bmc1_min_bound                        0
% 2.75/1.00  --bmc1_max_bound                        -1
% 2.75/1.00  --bmc1_max_bound_default                -1
% 2.75/1.00  --bmc1_symbol_reachability              true
% 2.75/1.00  --bmc1_property_lemmas                  false
% 2.75/1.00  --bmc1_k_induction                      false
% 2.75/1.00  --bmc1_non_equiv_states                 false
% 2.75/1.00  --bmc1_deadlock                         false
% 2.75/1.00  --bmc1_ucm                              false
% 2.75/1.00  --bmc1_add_unsat_core                   none
% 2.75/1.00  --bmc1_unsat_core_children              false
% 2.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/1.00  --bmc1_out_stat                         full
% 2.75/1.00  --bmc1_ground_init                      false
% 2.75/1.00  --bmc1_pre_inst_next_state              false
% 2.75/1.00  --bmc1_pre_inst_state                   false
% 2.75/1.00  --bmc1_pre_inst_reach_state             false
% 2.75/1.00  --bmc1_out_unsat_core                   false
% 2.75/1.00  --bmc1_aig_witness_out                  false
% 2.75/1.00  --bmc1_verbose                          false
% 2.75/1.00  --bmc1_dump_clauses_tptp                false
% 2.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.75/1.00  --bmc1_dump_file                        -
% 2.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.75/1.00  --bmc1_ucm_extend_mode                  1
% 2.75/1.00  --bmc1_ucm_init_mode                    2
% 2.75/1.00  --bmc1_ucm_cone_mode                    none
% 2.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.75/1.00  --bmc1_ucm_relax_model                  4
% 2.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/1.00  --bmc1_ucm_layered_model                none
% 2.75/1.00  --bmc1_ucm_max_lemma_size               10
% 2.75/1.00  
% 2.75/1.00  ------ AIG Options
% 2.75/1.00  
% 2.75/1.00  --aig_mode                              false
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation Options
% 2.75/1.00  
% 2.75/1.00  --instantiation_flag                    true
% 2.75/1.00  --inst_sos_flag                         false
% 2.75/1.00  --inst_sos_phase                        true
% 2.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel_side                     none
% 2.75/1.00  --inst_solver_per_active                1400
% 2.75/1.00  --inst_solver_calls_frac                1.
% 2.75/1.00  --inst_passive_queue_type               priority_queues
% 2.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/1.00  --inst_passive_queues_freq              [25;2]
% 2.75/1.00  --inst_dismatching                      true
% 2.75/1.00  --inst_eager_unprocessed_to_passive     true
% 2.75/1.00  --inst_prop_sim_given                   true
% 2.75/1.00  --inst_prop_sim_new                     false
% 2.75/1.00  --inst_subs_new                         false
% 2.75/1.00  --inst_eq_res_simp                      false
% 2.75/1.00  --inst_subs_given                       false
% 2.75/1.00  --inst_orphan_elimination               true
% 2.75/1.00  --inst_learning_loop_flag               true
% 2.75/1.00  --inst_learning_start                   3000
% 2.75/1.00  --inst_learning_factor                  2
% 2.75/1.00  --inst_start_prop_sim_after_learn       3
% 2.75/1.00  --inst_sel_renew                        solver
% 2.75/1.00  --inst_lit_activity_flag                true
% 2.75/1.00  --inst_restr_to_given                   false
% 2.75/1.00  --inst_activity_threshold               500
% 2.75/1.00  --inst_out_proof                        true
% 2.75/1.00  
% 2.75/1.00  ------ Resolution Options
% 2.75/1.00  
% 2.75/1.00  --resolution_flag                       false
% 2.75/1.00  --res_lit_sel                           adaptive
% 2.75/1.00  --res_lit_sel_side                      none
% 2.75/1.00  --res_ordering                          kbo
% 2.75/1.00  --res_to_prop_solver                    active
% 2.75/1.00  --res_prop_simpl_new                    false
% 2.75/1.00  --res_prop_simpl_given                  true
% 2.75/1.00  --res_passive_queue_type                priority_queues
% 2.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/1.00  --res_passive_queues_freq               [15;5]
% 2.75/1.00  --res_forward_subs                      full
% 2.75/1.00  --res_backward_subs                     full
% 2.75/1.00  --res_forward_subs_resolution           true
% 2.75/1.00  --res_backward_subs_resolution          true
% 2.75/1.00  --res_orphan_elimination                true
% 2.75/1.00  --res_time_limit                        2.
% 2.75/1.00  --res_out_proof                         true
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Options
% 2.75/1.00  
% 2.75/1.00  --superposition_flag                    true
% 2.75/1.00  --sup_passive_queue_type                priority_queues
% 2.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.75/1.00  --demod_completeness_check              fast
% 2.75/1.00  --demod_use_ground                      true
% 2.75/1.00  --sup_to_prop_solver                    passive
% 2.75/1.00  --sup_prop_simpl_new                    true
% 2.75/1.00  --sup_prop_simpl_given                  true
% 2.75/1.00  --sup_fun_splitting                     false
% 2.75/1.00  --sup_smt_interval                      50000
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Simplification Setup
% 2.75/1.00  
% 2.75/1.00  --sup_indices_passive                   []
% 2.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_full_bw                           [BwDemod]
% 2.75/1.00  --sup_immed_triv                        [TrivRules]
% 2.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_immed_bw_main                     []
% 2.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  
% 2.75/1.00  ------ Combination Options
% 2.75/1.00  
% 2.75/1.00  --comb_res_mult                         3
% 2.75/1.00  --comb_sup_mult                         2
% 2.75/1.00  --comb_inst_mult                        10
% 2.75/1.00  
% 2.75/1.00  ------ Debug Options
% 2.75/1.00  
% 2.75/1.00  --dbg_backtrace                         false
% 2.75/1.00  --dbg_dump_prop_clauses                 false
% 2.75/1.00  --dbg_dump_prop_clauses_file            -
% 2.75/1.00  --dbg_out_stat                          false
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ Proving...
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS status Theorem for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  fof(f13,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f28,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f13])).
% 2.75/1.00  
% 2.75/1.00  fof(f29,plain,(
% 2.75/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(flattening,[],[f28])).
% 2.75/1.00  
% 2.75/1.00  fof(f43,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(nnf_transformation,[],[f29])).
% 2.75/1.00  
% 2.75/1.00  fof(f67,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f43])).
% 2.75/1.00  
% 2.75/1.00  fof(f14,conjecture,(
% 2.75/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f15,negated_conjecture,(
% 2.75/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.75/1.00    inference(negated_conjecture,[],[f14])).
% 2.75/1.00  
% 2.75/1.00  fof(f30,plain,(
% 2.75/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.75/1.00    inference(ennf_transformation,[],[f15])).
% 2.75/1.00  
% 2.75/1.00  fof(f31,plain,(
% 2.75/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.75/1.00    inference(flattening,[],[f30])).
% 2.75/1.00  
% 2.75/1.00  fof(f45,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f44,plain,(
% 2.75/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f46,plain,(
% 2.75/1.00    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f45,f44])).
% 2.75/1.00  
% 2.75/1.00  fof(f77,plain,(
% 2.75/1.00    v1_funct_2(sK5,sK2,sK3)),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f78,plain,(
% 2.75/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f11,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f25,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f11])).
% 2.75/1.00  
% 2.75/1.00  fof(f64,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f25])).
% 2.75/1.00  
% 2.75/1.00  fof(f74,plain,(
% 2.75/1.00    v1_funct_2(sK4,sK2,sK3)),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f75,plain,(
% 2.75/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f9,axiom,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f22,plain,(
% 2.75/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f9])).
% 2.75/1.00  
% 2.75/1.00  fof(f23,plain,(
% 2.75/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/1.00    inference(flattening,[],[f22])).
% 2.75/1.00  
% 2.75/1.00  fof(f40,plain,(
% 2.75/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f41,plain,(
% 2.75/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f61,plain,(
% 2.75/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f41])).
% 2.75/1.00  
% 2.75/1.00  fof(f76,plain,(
% 2.75/1.00    v1_funct_1(sK5)),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f10,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f24,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f10])).
% 2.75/1.00  
% 2.75/1.00  fof(f63,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f24])).
% 2.75/1.00  
% 2.75/1.00  fof(f73,plain,(
% 2.75/1.00    v1_funct_1(sK4)),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f12,axiom,(
% 2.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f26,plain,(
% 2.75/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.75/1.00    inference(ennf_transformation,[],[f12])).
% 2.75/1.00  
% 2.75/1.00  fof(f27,plain,(
% 2.75/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(flattening,[],[f26])).
% 2.75/1.00  
% 2.75/1.00  fof(f42,plain,(
% 2.75/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(nnf_transformation,[],[f27])).
% 2.75/1.00  
% 2.75/1.00  fof(f66,plain,(
% 2.75/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f42])).
% 2.75/1.00  
% 2.75/1.00  fof(f85,plain,(
% 2.75/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(equality_resolution,[],[f66])).
% 2.75/1.00  
% 2.75/1.00  fof(f80,plain,(
% 2.75/1.00    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f79,plain,(
% 2.75/1.00    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f46])).
% 2.75/1.00  
% 2.75/1.00  fof(f62,plain,(
% 2.75/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f41])).
% 2.75/1.00  
% 2.75/1.00  fof(f2,axiom,(
% 2.75/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f18,plain,(
% 2.75/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f2])).
% 2.75/1.00  
% 2.75/1.00  fof(f32,plain,(
% 2.75/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/1.00    inference(nnf_transformation,[],[f18])).
% 2.75/1.00  
% 2.75/1.00  fof(f33,plain,(
% 2.75/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/1.00    inference(rectify,[],[f32])).
% 2.75/1.00  
% 2.75/1.00  fof(f34,plain,(
% 2.75/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f35,plain,(
% 2.75/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.75/1.00  
% 2.75/1.00  fof(f49,plain,(
% 2.75/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f35])).
% 2.75/1.00  
% 2.75/1.00  fof(f6,axiom,(
% 2.75/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f19,plain,(
% 2.75/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f6])).
% 2.75/1.00  
% 2.75/1.00  fof(f58,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f19])).
% 2.75/1.00  
% 2.75/1.00  fof(f50,plain,(
% 2.75/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f35])).
% 2.75/1.00  
% 2.75/1.00  fof(f5,axiom,(
% 2.75/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f38,plain,(
% 2.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.75/1.00    inference(nnf_transformation,[],[f5])).
% 2.75/1.00  
% 2.75/1.00  fof(f39,plain,(
% 2.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.75/1.00    inference(flattening,[],[f38])).
% 2.75/1.00  
% 2.75/1.00  fof(f57,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.75/1.00    inference(cnf_transformation,[],[f39])).
% 2.75/1.00  
% 2.75/1.00  fof(f83,plain,(
% 2.75/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.75/1.00    inference(equality_resolution,[],[f57])).
% 2.75/1.00  
% 2.75/1.00  fof(f1,axiom,(
% 2.75/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f16,plain,(
% 2.75/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.75/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.75/1.00  
% 2.75/1.00  fof(f17,plain,(
% 2.75/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.75/1.00    inference(ennf_transformation,[],[f16])).
% 2.75/1.00  
% 2.75/1.00  fof(f47,plain,(
% 2.75/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f17])).
% 2.75/1.00  
% 2.75/1.00  fof(f3,axiom,(
% 2.75/1.00    v1_xboole_0(k1_xboole_0)),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f51,plain,(
% 2.75/1.00    v1_xboole_0(k1_xboole_0)),
% 2.75/1.00    inference(cnf_transformation,[],[f3])).
% 2.75/1.00  
% 2.75/1.00  fof(f4,axiom,(
% 2.75/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.75/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f36,plain,(
% 2.75/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/1.00    inference(nnf_transformation,[],[f4])).
% 2.75/1.00  
% 2.75/1.00  fof(f37,plain,(
% 2.75/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/1.00    inference(flattening,[],[f36])).
% 2.75/1.00  
% 2.75/1.00  fof(f54,plain,(
% 2.75/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f37])).
% 2.75/1.00  
% 2.75/1.00  cnf(c_25,plain,
% 2.75/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.75/1.00      | k1_xboole_0 = X2 ),
% 2.75/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_29,negated_conjecture,
% 2.75/1.00      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.75/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_432,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.75/1.00      | sK5 != X0
% 2.75/1.00      | sK3 != X2
% 2.75/1.00      | sK2 != X1
% 2.75/1.00      | k1_xboole_0 = X2 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_433,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.75/1.00      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.75/1.00      | k1_xboole_0 = sK3 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_432]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_28,negated_conjecture,
% 2.75/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_435,plain,
% 2.75/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_433,c_28]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1007,plain,
% 2.75/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_17,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1009,plain,
% 2.75/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1867,plain,
% 2.75/1.00      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1007,c_1009]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2007,plain,
% 2.75/1.00      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_435,c_1867]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_32,negated_conjecture,
% 2.75/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.75/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_443,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.75/1.00      | sK4 != X0
% 2.75/1.00      | sK3 != X2
% 2.75/1.00      | sK2 != X1
% 2.75/1.00      | k1_xboole_0 = X2 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_444,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.75/1.00      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.75/1.00      | k1_xboole_0 = sK3 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_443]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_31,negated_conjecture,
% 2.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_446,plain,
% 2.75/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_444,c_31]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1005,plain,
% 2.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1868,plain,
% 2.75/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1005,c_1009]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2144,plain,
% 2.75/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_446,c_1868]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_15,plain,
% 2.75/1.00      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.75/1.00      | ~ v1_relat_1(X1)
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X1)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | X0 = X1
% 2.75/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1011,plain,
% 2.75/1.00      ( X0 = X1
% 2.75/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.75/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top
% 2.75/1.00      | v1_relat_1(X1) != iProver_top
% 2.75/1.00      | v1_funct_1(X1) != iProver_top
% 2.75/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2461,plain,
% 2.75/1.00      ( k1_relat_1(X0) != sK2
% 2.75/1.00      | sK5 = X0
% 2.75/1.00      | sK3 = k1_xboole_0
% 2.75/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top
% 2.75/1.00      | v1_relat_1(sK5) != iProver_top
% 2.75/1.00      | v1_funct_1(X0) != iProver_top
% 2.75/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2007,c_1011]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_30,negated_conjecture,
% 2.75/1.00      ( v1_funct_1(sK5) ),
% 2.75/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_37,plain,
% 2.75/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_39,plain,
% 2.75/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_16,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | v1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1217,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.75/1.00      | v1_relat_1(sK5) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1218,plain,
% 2.75/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.75/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1217]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2750,plain,
% 2.75/1.00      ( v1_funct_1(X0) != iProver_top
% 2.75/1.00      | k1_relat_1(X0) != sK2
% 2.75/1.00      | sK5 = X0
% 2.75/1.00      | sK3 = k1_xboole_0
% 2.75/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_2461,c_37,c_39,c_1218]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2751,plain,
% 2.75/1.00      ( k1_relat_1(X0) != sK2
% 2.75/1.00      | sK5 = X0
% 2.75/1.00      | sK3 = k1_xboole_0
% 2.75/1.00      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top
% 2.75/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.75/1.00      inference(renaming,[status(thm)],[c_2750]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2763,plain,
% 2.75/1.00      ( sK5 = sK4
% 2.75/1.00      | sK3 = k1_xboole_0
% 2.75/1.00      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.75/1.00      | v1_relat_1(sK4) != iProver_top
% 2.75/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2144,c_2751]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_33,negated_conjecture,
% 2.75/1.00      ( v1_funct_1(sK4) ),
% 2.75/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_34,plain,
% 2.75/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_36,plain,
% 2.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_18,plain,
% 2.75/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.75/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_26,negated_conjecture,
% 2.75/1.00      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.75/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_349,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | sK5 != X0
% 2.75/1.00      | sK4 != X0
% 2.75/1.00      | sK3 != X2
% 2.75/1.00      | sK2 != X1 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_350,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.75/1.00      | sK4 != sK5 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1220,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.75/1.00      | v1_relat_1(sK4) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1221,plain,
% 2.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.75/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_624,plain,( X0 = X0 ),theory(equality) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1362,plain,
% 2.75/1.00      ( sK4 = sK4 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_625,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1246,plain,
% 2.75/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1660,plain,
% 2.75/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1246]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2824,plain,
% 2.75/1.00      ( sK3 = k1_xboole_0
% 2.75/1.00      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_2763,c_34,c_36,c_28,c_350,c_1221,c_1362,c_1660]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2830,plain,
% 2.75/1.00      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2144,c_2824]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_27,negated_conjecture,
% 2.75/1.00      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1008,plain,
% 2.75/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.75/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2850,plain,
% 2.75/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.75/1.00      | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2830,c_1008]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_14,plain,
% 2.75/1.00      ( ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_relat_1(X1)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X1)
% 2.75/1.00      | X1 = X0
% 2.75/1.00      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.75/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.75/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1012,plain,
% 2.75/1.00      ( X0 = X1
% 2.75/1.00      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.75/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.75/1.00      | v1_relat_1(X1) != iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top
% 2.75/1.00      | v1_funct_1(X0) != iProver_top
% 2.75/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3083,plain,
% 2.75/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.75/1.00      | sK5 = sK4
% 2.75/1.00      | sK3 = k1_xboole_0
% 2.75/1.00      | v1_relat_1(sK5) != iProver_top
% 2.75/1.00      | v1_relat_1(sK4) != iProver_top
% 2.75/1.00      | v1_funct_1(sK5) != iProver_top
% 2.75/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2850,c_1012]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3099,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK5)
% 2.75/1.00      | ~ v1_relat_1(sK4)
% 2.75/1.00      | ~ v1_funct_1(sK5)
% 2.75/1.00      | ~ v1_funct_1(sK4)
% 2.75/1.00      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.75/1.00      | sK5 = sK4
% 2.75/1.00      | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3083]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4154,plain,
% 2.75/1.00      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_3083,c_33,c_31,c_30,c_28,c_350,c_1217,c_1220,c_1362,
% 2.75/1.00                 c_1660,c_3099]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4158,plain,
% 2.75/1.00      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2007,c_4154]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4159,plain,
% 2.75/1.00      ( sK3 = k1_xboole_0 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_4158,c_2144]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2,plain,
% 2.75/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1019,plain,
% 2.75/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_11,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.75/1.00      | ~ r2_hidden(X2,X0)
% 2.75/1.00      | r2_hidden(X2,X1) ),
% 2.75/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1015,plain,
% 2.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.75/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.75/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3240,plain,
% 2.75/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.75/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1005,c_1015]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1,plain,
% 2.75/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 2.75/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1020,plain,
% 2.75/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3446,plain,
% 2.75/1.00      ( r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK4) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3240,c_1020]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3583,plain,
% 2.75/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1019,c_3446]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4165,plain,
% 2.75/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4159,c_3583]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_8,plain,
% 2.75/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.75/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4272,plain,
% 2.75/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4165,c_8]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3239,plain,
% 2.75/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.75/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1007,c_1015]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3425,plain,
% 2.75/1.00      ( r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK5) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3239,c_1020]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3542,plain,
% 2.75/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1019,c_3425]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4166,plain,
% 2.75/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4159,c_3542]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4269,plain,
% 2.75/1.00      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4166,c_8]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_0,plain,
% 2.75/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.75/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4,plain,
% 2.75/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_336,plain,
% 2.75/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_337,plain,
% 2.75/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_336]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3195,plain,
% 2.75/1.00      ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_337]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3198,plain,
% 2.75/1.00      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_3195]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2911,plain,
% 2.75/1.00      ( ~ r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_337]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2914,plain,
% 2.75/1.00      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2911]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_5,plain,
% 2.75/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.75/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1594,plain,
% 2.75/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1595,plain,
% 2.75/1.00      ( sK4 = X0
% 2.75/1.00      | r1_tarski(X0,sK4) != iProver_top
% 2.75/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1597,plain,
% 2.75/1.00      ( sK4 = k1_xboole_0
% 2.75/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.75/1.00      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1565,plain,
% 2.75/1.00      ( r1_tarski(X0,sK4) | r2_hidden(sK0(X0,sK4),X0) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1571,plain,
% 2.75/1.00      ( r1_tarski(X0,sK4) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,sK4),X0) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1565]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1573,plain,
% 2.75/1.00      ( r1_tarski(k1_xboole_0,sK4) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1571]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1554,plain,
% 2.75/1.00      ( r1_tarski(X0,sK5) | r2_hidden(sK0(X0,sK5),X0) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1560,plain,
% 2.75/1.00      ( r1_tarski(X0,sK5) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(X0,sK5),X0) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1554]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1562,plain,
% 2.75/1.00      ( r1_tarski(k1_xboole_0,sK5) = iProver_top
% 2.75/1.00      | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1560]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1453,plain,
% 2.75/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1454,plain,
% 2.75/1.00      ( sK5 = X0
% 2.75/1.00      | r1_tarski(X0,sK5) != iProver_top
% 2.75/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1456,plain,
% 2.75/1.00      ( sK5 = k1_xboole_0
% 2.75/1.00      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.75/1.00      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1454]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1247,plain,
% 2.75/1.00      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1246]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(contradiction,plain,
% 2.75/1.00      ( $false ),
% 2.75/1.00      inference(minisat,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_4272,c_4269,c_3198,c_2914,c_1597,c_1573,c_1562,c_1456,
% 2.75/1.00                 c_1247,c_350,c_28]) ).
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  ------                               Statistics
% 2.75/1.00  
% 2.75/1.00  ------ General
% 2.75/1.00  
% 2.75/1.00  abstr_ref_over_cycles:                  0
% 2.75/1.00  abstr_ref_under_cycles:                 0
% 2.75/1.00  gc_basic_clause_elim:                   0
% 2.75/1.00  forced_gc_time:                         0
% 2.75/1.00  parsing_time:                           0.01
% 2.75/1.00  unif_index_cands_time:                  0.
% 2.75/1.00  unif_index_add_time:                    0.
% 2.75/1.00  orderings_time:                         0.
% 2.75/1.00  out_proof_time:                         0.012
% 2.75/1.00  total_time:                             0.166
% 2.75/1.00  num_of_symbols:                         51
% 2.75/1.00  num_of_terms:                           4328
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing
% 2.75/1.00  
% 2.75/1.00  num_of_splits:                          0
% 2.75/1.00  num_of_split_atoms:                     0
% 2.75/1.00  num_of_reused_defs:                     0
% 2.75/1.00  num_eq_ax_congr_red:                    26
% 2.75/1.00  num_of_sem_filtered_clauses:            1
% 2.75/1.00  num_of_subtypes:                        0
% 2.75/1.00  monotx_restored_types:                  0
% 2.75/1.00  sat_num_of_epr_types:                   0
% 2.75/1.00  sat_num_of_non_cyclic_types:            0
% 2.75/1.00  sat_guarded_non_collapsed_types:        0
% 2.75/1.00  num_pure_diseq_elim:                    0
% 2.75/1.00  simp_replaced_by:                       0
% 2.75/1.00  res_preprocessed:                       136
% 2.75/1.00  prep_upred:                             0
% 2.75/1.00  prep_unflattend:                        42
% 2.75/1.00  smt_new_axioms:                         0
% 2.75/1.00  pred_elim_cands:                        5
% 2.75/1.00  pred_elim:                              3
% 2.75/1.00  pred_elim_cl:                           5
% 2.75/1.00  pred_elim_cycles:                       5
% 2.75/1.00  merged_defs:                            0
% 2.75/1.00  merged_defs_ncl:                        0
% 2.75/1.00  bin_hyper_res:                          0
% 2.75/1.00  prep_cycles:                            4
% 2.75/1.00  pred_elim_time:                         0.003
% 2.75/1.00  splitting_time:                         0.
% 2.75/1.00  sem_filter_time:                        0.
% 2.75/1.00  monotx_time:                            0.
% 2.75/1.00  subtype_inf_time:                       0.
% 2.75/1.00  
% 2.75/1.00  ------ Problem properties
% 2.75/1.00  
% 2.75/1.00  clauses:                                28
% 2.75/1.00  conjectures:                            5
% 2.75/1.00  epr:                                    7
% 2.75/1.00  horn:                                   21
% 2.75/1.00  ground:                                 11
% 2.75/1.00  unary:                                  10
% 2.75/1.00  binary:                                 7
% 2.75/1.00  lits:                                   67
% 2.75/1.00  lits_eq:                                28
% 2.75/1.00  fd_pure:                                0
% 2.75/1.00  fd_pseudo:                              0
% 2.75/1.00  fd_cond:                                1
% 2.75/1.00  fd_pseudo_cond:                         3
% 2.75/1.00  ac_symbols:                             0
% 2.75/1.00  
% 2.75/1.00  ------ Propositional Solver
% 2.75/1.00  
% 2.75/1.00  prop_solver_calls:                      27
% 2.75/1.00  prop_fast_solver_calls:                 892
% 2.75/1.00  smt_solver_calls:                       0
% 2.75/1.00  smt_fast_solver_calls:                  0
% 2.75/1.00  prop_num_of_clauses:                    1574
% 2.75/1.00  prop_preprocess_simplified:             4931
% 2.75/1.00  prop_fo_subsumed:                       21
% 2.75/1.00  prop_solver_time:                       0.
% 2.75/1.00  smt_solver_time:                        0.
% 2.75/1.00  smt_fast_solver_time:                   0.
% 2.75/1.00  prop_fast_solver_time:                  0.
% 2.75/1.00  prop_unsat_core_time:                   0.
% 2.75/1.00  
% 2.75/1.00  ------ QBF
% 2.75/1.00  
% 2.75/1.00  qbf_q_res:                              0
% 2.75/1.00  qbf_num_tautologies:                    0
% 2.75/1.00  qbf_prep_cycles:                        0
% 2.75/1.00  
% 2.75/1.00  ------ BMC1
% 2.75/1.00  
% 2.75/1.00  bmc1_current_bound:                     -1
% 2.75/1.00  bmc1_last_solved_bound:                 -1
% 2.75/1.00  bmc1_unsat_core_size:                   -1
% 2.75/1.00  bmc1_unsat_core_parents_size:           -1
% 2.75/1.00  bmc1_merge_next_fun:                    0
% 2.75/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation
% 2.75/1.00  
% 2.75/1.00  inst_num_of_clauses:                    564
% 2.75/1.00  inst_num_in_passive:                    31
% 2.75/1.00  inst_num_in_active:                     280
% 2.75/1.00  inst_num_in_unprocessed:                253
% 2.75/1.00  inst_num_of_loops:                      330
% 2.75/1.00  inst_num_of_learning_restarts:          0
% 2.75/1.00  inst_num_moves_active_passive:          47
% 2.75/1.00  inst_lit_activity:                      0
% 2.75/1.00  inst_lit_activity_moves:                0
% 2.75/1.00  inst_num_tautologies:                   0
% 2.75/1.00  inst_num_prop_implied:                  0
% 2.75/1.00  inst_num_existing_simplified:           0
% 2.75/1.00  inst_num_eq_res_simplified:             0
% 2.75/1.00  inst_num_child_elim:                    0
% 2.75/1.00  inst_num_of_dismatching_blockings:      140
% 2.75/1.00  inst_num_of_non_proper_insts:           509
% 2.75/1.00  inst_num_of_duplicates:                 0
% 2.75/1.00  inst_inst_num_from_inst_to_res:         0
% 2.75/1.00  inst_dismatching_checking_time:         0.
% 2.75/1.00  
% 2.75/1.00  ------ Resolution
% 2.75/1.00  
% 2.75/1.00  res_num_of_clauses:                     0
% 2.75/1.00  res_num_in_passive:                     0
% 2.75/1.00  res_num_in_active:                      0
% 2.75/1.00  res_num_of_loops:                       140
% 2.75/1.00  res_forward_subset_subsumed:            64
% 2.75/1.00  res_backward_subset_subsumed:           0
% 2.75/1.00  res_forward_subsumed:                   0
% 2.75/1.00  res_backward_subsumed:                  0
% 2.75/1.00  res_forward_subsumption_resolution:     0
% 2.75/1.00  res_backward_subsumption_resolution:    0
% 2.75/1.00  res_clause_to_clause_subsumption:       194
% 2.75/1.00  res_orphan_elimination:                 0
% 2.75/1.00  res_tautology_del:                      32
% 2.75/1.00  res_num_eq_res_simplified:              0
% 2.75/1.00  res_num_sel_changes:                    0
% 2.75/1.00  res_moves_from_active_to_pass:          0
% 2.75/1.00  
% 2.75/1.00  ------ Superposition
% 2.75/1.00  
% 2.75/1.00  sup_time_total:                         0.
% 2.75/1.00  sup_time_generating:                    0.
% 2.75/1.00  sup_time_sim_full:                      0.
% 2.75/1.00  sup_time_sim_immed:                     0.
% 2.75/1.00  
% 2.75/1.00  sup_num_of_clauses:                     58
% 2.75/1.00  sup_num_in_active:                      35
% 2.75/1.00  sup_num_in_passive:                     23
% 2.75/1.00  sup_num_of_loops:                       65
% 2.75/1.00  sup_fw_superposition:                   52
% 2.75/1.00  sup_bw_superposition:                   17
% 2.75/1.00  sup_immediate_simplified:               23
% 2.75/1.00  sup_given_eliminated:                   0
% 2.75/1.00  comparisons_done:                       0
% 2.75/1.00  comparisons_avoided:                    14
% 2.75/1.00  
% 2.75/1.00  ------ Simplifications
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  sim_fw_subset_subsumed:                 3
% 2.75/1.00  sim_bw_subset_subsumed:                 8
% 2.75/1.00  sim_fw_subsumed:                        2
% 2.75/1.00  sim_bw_subsumed:                        0
% 2.75/1.00  sim_fw_subsumption_res:                 4
% 2.75/1.00  sim_bw_subsumption_res:                 0
% 2.75/1.00  sim_tautology_del:                      0
% 2.75/1.00  sim_eq_tautology_del:                   16
% 2.75/1.00  sim_eq_res_simp:                        2
% 2.75/1.00  sim_fw_demodulated:                     18
% 2.75/1.00  sim_bw_demodulated:                     26
% 2.75/1.00  sim_light_normalised:                   0
% 2.75/1.00  sim_joinable_taut:                      0
% 2.75/1.00  sim_joinable_simp:                      0
% 2.75/1.00  sim_ac_normalised:                      0
% 2.75/1.00  sim_smt_subsumption:                    0
% 2.75/1.00  
%------------------------------------------------------------------------------
