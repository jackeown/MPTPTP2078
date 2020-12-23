%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:15 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  184 (3205 expanded)
%              Number of clauses        :  122 (1051 expanded)
%              Number of leaves         :   16 ( 787 expanded)
%              Depth                    :   31
%              Number of atoms          :  635 (20660 expanded)
%              Number of equality atoms :  373 (5456 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                ( r2_hidden(X4,X0)
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
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f39,f38])).

fof(f67,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f70,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_451,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_796,plain,
    ( k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != sK5
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_451])).

cnf(c_797,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_1442,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_797])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_486,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_487,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_1614,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_487])).

cnf(c_2484,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1442,c_1614])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_508,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_881,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_508])).

cnf(c_882,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_1437,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_882])).

cnf(c_543,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_544,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1617,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_544])).

cnf(c_2360,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1437,c_1617])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1370,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2595,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_1370])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1062,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1601,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_495,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_496,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1605,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_1606,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1605])).

cnf(c_3278,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_33,c_1601,c_1606])).

cnf(c_3279,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3278])).

cnf(c_3291,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_3279])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_304,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_552,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_553,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_1604,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_1608,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1604])).

cnf(c_2074,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1063,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1906,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_2073,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_2786,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_3318,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_30,c_24,c_304,c_1601,c_1608,c_2074,c_2786])).

cnf(c_3324,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_3318])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1368,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3351,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3324,c_1368])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1371,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3402,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_1371])).

cnf(c_3403,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3402])).

cnf(c_3405,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3402,c_29,c_26,c_24,c_304,c_1601,c_1605,c_1604,c_2074,c_2786,c_3403])).

cnf(c_3409,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2484,c_3405])).

cnf(c_3457,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3409,c_2360])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1375,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_421,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1365,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_2356,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1365])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1376,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2795,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK5) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_1376])).

cnf(c_3015,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_2795])).

cnf(c_3464,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3457,c_3015])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_616,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_617,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_896,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_617])).

cnf(c_897,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1473,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
    | sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_897,c_5])).

cnf(c_598,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_599,plain,
    ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_821,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 != sK5
    | sK5 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_599])).

cnf(c_822,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK5 = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_1482,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
    | sK5 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_822,c_5])).

cnf(c_1628,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1629,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_2526,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_24,c_304,c_1482,c_1629])).

cnf(c_3473,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3457,c_2526])).

cnf(c_3552,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3473])).

cnf(c_3555,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3552,c_5])).

cnf(c_3556,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3555])).

cnf(c_3628,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3464,c_3556])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3630,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3628,c_6])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_436,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1364,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2298,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1364])).

cnf(c_2680,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_1376])).

cnf(c_2964,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_2680])).

cnf(c_3465,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3457,c_2964])).

cnf(c_3624,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3465,c_3556])).

cnf(c_3626,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3624,c_6])).

cnf(c_2421,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1854,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_2420,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_2422,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_2075,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1695,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1698,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1695])).

cnf(c_1674,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1677,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1674])).

cnf(c_1632,plain,
    ( sK5 != X0
    | sK5 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1633,plain,
    ( sK5 = sK4
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3630,c_3626,c_2786,c_2421,c_2422,c_2074,c_2075,c_1698,c_1677,c_1633,c_304,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:33:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.52/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.98  
% 2.52/0.98  ------  iProver source info
% 2.52/0.98  
% 2.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.98  git: non_committed_changes: false
% 2.52/0.98  git: last_make_outside_of_git: false
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options
% 2.52/0.98  
% 2.52/0.98  --out_options                           all
% 2.52/0.98  --tptp_safe_out                         true
% 2.52/0.98  --problem_path                          ""
% 2.52/0.98  --include_path                          ""
% 2.52/0.98  --clausifier                            res/vclausify_rel
% 2.52/0.98  --clausifier_options                    --mode clausify
% 2.52/0.98  --stdin                                 false
% 2.52/0.98  --stats_out                             all
% 2.52/0.98  
% 2.52/0.98  ------ General Options
% 2.52/0.98  
% 2.52/0.98  --fof                                   false
% 2.52/0.98  --time_out_real                         305.
% 2.52/0.98  --time_out_virtual                      -1.
% 2.52/0.98  --symbol_type_check                     false
% 2.52/0.98  --clausify_out                          false
% 2.52/0.98  --sig_cnt_out                           false
% 2.52/0.98  --trig_cnt_out                          false
% 2.52/0.98  --trig_cnt_out_tolerance                1.
% 2.52/0.98  --trig_cnt_out_sk_spl                   false
% 2.52/0.98  --abstr_cl_out                          false
% 2.52/0.98  
% 2.52/0.98  ------ Global Options
% 2.52/0.98  
% 2.52/0.98  --schedule                              default
% 2.52/0.98  --add_important_lit                     false
% 2.52/0.98  --prop_solver_per_cl                    1000
% 2.52/0.98  --min_unsat_core                        false
% 2.52/0.98  --soft_assumptions                      false
% 2.52/0.98  --soft_lemma_size                       3
% 2.52/0.98  --prop_impl_unit_size                   0
% 2.52/0.98  --prop_impl_unit                        []
% 2.52/0.98  --share_sel_clauses                     true
% 2.52/0.98  --reset_solvers                         false
% 2.52/0.98  --bc_imp_inh                            [conj_cone]
% 2.52/0.98  --conj_cone_tolerance                   3.
% 2.52/0.98  --extra_neg_conj                        none
% 2.52/0.98  --large_theory_mode                     true
% 2.52/0.98  --prolific_symb_bound                   200
% 2.52/0.98  --lt_threshold                          2000
% 2.52/0.98  --clause_weak_htbl                      true
% 2.52/0.98  --gc_record_bc_elim                     false
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing Options
% 2.52/0.98  
% 2.52/0.98  --preprocessing_flag                    true
% 2.52/0.98  --time_out_prep_mult                    0.1
% 2.52/0.98  --splitting_mode                        input
% 2.52/0.98  --splitting_grd                         true
% 2.52/0.98  --splitting_cvd                         false
% 2.52/0.98  --splitting_cvd_svl                     false
% 2.52/0.98  --splitting_nvd                         32
% 2.52/0.98  --sub_typing                            true
% 2.52/0.98  --prep_gs_sim                           true
% 2.52/0.98  --prep_unflatten                        true
% 2.52/0.98  --prep_res_sim                          true
% 2.52/0.98  --prep_upred                            true
% 2.52/0.98  --prep_sem_filter                       exhaustive
% 2.52/0.98  --prep_sem_filter_out                   false
% 2.52/0.98  --pred_elim                             true
% 2.52/0.98  --res_sim_input                         true
% 2.52/0.98  --eq_ax_congr_red                       true
% 2.52/0.98  --pure_diseq_elim                       true
% 2.52/0.98  --brand_transform                       false
% 2.52/0.98  --non_eq_to_eq                          false
% 2.52/0.98  --prep_def_merge                        true
% 2.52/0.98  --prep_def_merge_prop_impl              false
% 2.52/0.98  --prep_def_merge_mbd                    true
% 2.52/0.98  --prep_def_merge_tr_red                 false
% 2.52/0.98  --prep_def_merge_tr_cl                  false
% 2.52/0.98  --smt_preprocessing                     true
% 2.52/0.98  --smt_ac_axioms                         fast
% 2.52/0.98  --preprocessed_out                      false
% 2.52/0.98  --preprocessed_stats                    false
% 2.52/0.98  
% 2.52/0.98  ------ Abstraction refinement Options
% 2.52/0.98  
% 2.52/0.98  --abstr_ref                             []
% 2.52/0.98  --abstr_ref_prep                        false
% 2.52/0.98  --abstr_ref_until_sat                   false
% 2.52/0.98  --abstr_ref_sig_restrict                funpre
% 2.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.98  --abstr_ref_under                       []
% 2.52/0.98  
% 2.52/0.98  ------ SAT Options
% 2.52/0.98  
% 2.52/0.98  --sat_mode                              false
% 2.52/0.98  --sat_fm_restart_options                ""
% 2.52/0.98  --sat_gr_def                            false
% 2.52/0.98  --sat_epr_types                         true
% 2.52/0.98  --sat_non_cyclic_types                  false
% 2.52/0.98  --sat_finite_models                     false
% 2.52/0.98  --sat_fm_lemmas                         false
% 2.52/0.98  --sat_fm_prep                           false
% 2.52/0.98  --sat_fm_uc_incr                        true
% 2.52/0.98  --sat_out_model                         small
% 2.52/0.98  --sat_out_clauses                       false
% 2.52/0.98  
% 2.52/0.98  ------ QBF Options
% 2.52/0.98  
% 2.52/0.98  --qbf_mode                              false
% 2.52/0.98  --qbf_elim_univ                         false
% 2.52/0.98  --qbf_dom_inst                          none
% 2.52/0.98  --qbf_dom_pre_inst                      false
% 2.52/0.98  --qbf_sk_in                             false
% 2.52/0.98  --qbf_pred_elim                         true
% 2.52/0.98  --qbf_split                             512
% 2.52/0.98  
% 2.52/0.98  ------ BMC1 Options
% 2.52/0.98  
% 2.52/0.98  --bmc1_incremental                      false
% 2.52/0.98  --bmc1_axioms                           reachable_all
% 2.52/0.98  --bmc1_min_bound                        0
% 2.52/0.98  --bmc1_max_bound                        -1
% 2.52/0.98  --bmc1_max_bound_default                -1
% 2.52/0.98  --bmc1_symbol_reachability              true
% 2.52/0.98  --bmc1_property_lemmas                  false
% 2.52/0.98  --bmc1_k_induction                      false
% 2.52/0.98  --bmc1_non_equiv_states                 false
% 2.52/0.98  --bmc1_deadlock                         false
% 2.52/0.98  --bmc1_ucm                              false
% 2.52/0.98  --bmc1_add_unsat_core                   none
% 2.52/0.98  --bmc1_unsat_core_children              false
% 2.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.98  --bmc1_out_stat                         full
% 2.52/0.98  --bmc1_ground_init                      false
% 2.52/0.98  --bmc1_pre_inst_next_state              false
% 2.52/0.98  --bmc1_pre_inst_state                   false
% 2.52/0.98  --bmc1_pre_inst_reach_state             false
% 2.52/0.98  --bmc1_out_unsat_core                   false
% 2.52/0.98  --bmc1_aig_witness_out                  false
% 2.52/0.98  --bmc1_verbose                          false
% 2.52/0.98  --bmc1_dump_clauses_tptp                false
% 2.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.98  --bmc1_dump_file                        -
% 2.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.98  --bmc1_ucm_extend_mode                  1
% 2.52/0.98  --bmc1_ucm_init_mode                    2
% 2.52/0.98  --bmc1_ucm_cone_mode                    none
% 2.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.98  --bmc1_ucm_relax_model                  4
% 2.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.98  --bmc1_ucm_layered_model                none
% 2.52/0.98  --bmc1_ucm_max_lemma_size               10
% 2.52/0.98  
% 2.52/0.98  ------ AIG Options
% 2.52/0.98  
% 2.52/0.98  --aig_mode                              false
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation Options
% 2.52/0.98  
% 2.52/0.98  --instantiation_flag                    true
% 2.52/0.98  --inst_sos_flag                         false
% 2.52/0.98  --inst_sos_phase                        true
% 2.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel_side                     num_symb
% 2.52/0.98  --inst_solver_per_active                1400
% 2.52/0.98  --inst_solver_calls_frac                1.
% 2.52/0.98  --inst_passive_queue_type               priority_queues
% 2.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.98  --inst_passive_queues_freq              [25;2]
% 2.52/0.98  --inst_dismatching                      true
% 2.52/0.98  --inst_eager_unprocessed_to_passive     true
% 2.52/0.98  --inst_prop_sim_given                   true
% 2.52/0.98  --inst_prop_sim_new                     false
% 2.52/0.98  --inst_subs_new                         false
% 2.52/0.98  --inst_eq_res_simp                      false
% 2.52/0.98  --inst_subs_given                       false
% 2.52/0.98  --inst_orphan_elimination               true
% 2.52/0.98  --inst_learning_loop_flag               true
% 2.52/0.98  --inst_learning_start                   3000
% 2.52/0.98  --inst_learning_factor                  2
% 2.52/0.98  --inst_start_prop_sim_after_learn       3
% 2.52/0.98  --inst_sel_renew                        solver
% 2.52/0.98  --inst_lit_activity_flag                true
% 2.52/0.98  --inst_restr_to_given                   false
% 2.52/0.98  --inst_activity_threshold               500
% 2.52/0.98  --inst_out_proof                        true
% 2.52/0.98  
% 2.52/0.98  ------ Resolution Options
% 2.52/0.98  
% 2.52/0.98  --resolution_flag                       true
% 2.52/0.98  --res_lit_sel                           adaptive
% 2.52/0.98  --res_lit_sel_side                      none
% 2.52/0.98  --res_ordering                          kbo
% 2.52/0.98  --res_to_prop_solver                    active
% 2.52/0.98  --res_prop_simpl_new                    false
% 2.52/0.98  --res_prop_simpl_given                  true
% 2.52/0.98  --res_passive_queue_type                priority_queues
% 2.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.98  --res_passive_queues_freq               [15;5]
% 2.52/0.98  --res_forward_subs                      full
% 2.52/0.98  --res_backward_subs                     full
% 2.52/0.98  --res_forward_subs_resolution           true
% 2.52/0.98  --res_backward_subs_resolution          true
% 2.52/0.98  --res_orphan_elimination                true
% 2.52/0.98  --res_time_limit                        2.
% 2.52/0.98  --res_out_proof                         true
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Options
% 2.52/0.98  
% 2.52/0.98  --superposition_flag                    true
% 2.52/0.98  --sup_passive_queue_type                priority_queues
% 2.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.98  --demod_completeness_check              fast
% 2.52/0.98  --demod_use_ground                      true
% 2.52/0.98  --sup_to_prop_solver                    passive
% 2.52/0.98  --sup_prop_simpl_new                    true
% 2.52/0.98  --sup_prop_simpl_given                  true
% 2.52/0.98  --sup_fun_splitting                     false
% 2.52/0.98  --sup_smt_interval                      50000
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Simplification Setup
% 2.52/0.98  
% 2.52/0.98  --sup_indices_passive                   []
% 2.52/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_full_bw                           [BwDemod]
% 2.52/0.98  --sup_immed_triv                        [TrivRules]
% 2.52/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_immed_bw_main                     []
% 2.52/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.98  
% 2.52/0.98  ------ Combination Options
% 2.52/0.98  
% 2.52/0.98  --comb_res_mult                         3
% 2.52/0.98  --comb_sup_mult                         2
% 2.52/0.98  --comb_inst_mult                        10
% 2.52/0.98  
% 2.52/0.98  ------ Debug Options
% 2.52/0.98  
% 2.52/0.98  --dbg_backtrace                         false
% 2.52/0.98  --dbg_dump_prop_clauses                 false
% 2.52/0.98  --dbg_dump_prop_clauses_file            -
% 2.52/0.98  --dbg_out_stat                          false
% 2.52/0.98  ------ Parsing...
% 2.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.98  ------ Proving...
% 2.52/0.98  ------ Problem Properties 
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  clauses                                 31
% 2.52/0.98  conjectures                             3
% 2.52/0.98  EPR                                     7
% 2.52/0.98  Horn                                    22
% 2.52/0.98  unary                                   6
% 2.52/0.98  binary                                  9
% 2.52/0.98  lits                                    88
% 2.52/0.98  lits eq                                 59
% 2.52/0.98  fd_pure                                 0
% 2.52/0.98  fd_pseudo                               0
% 2.52/0.98  fd_cond                                 2
% 2.52/0.98  fd_pseudo_cond                          2
% 2.52/0.98  AC symbols                              0
% 2.52/0.98  
% 2.52/0.98  ------ Schedule dynamic 5 is on 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  Current options:
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options
% 2.52/0.98  
% 2.52/0.98  --out_options                           all
% 2.52/0.98  --tptp_safe_out                         true
% 2.52/0.98  --problem_path                          ""
% 2.52/0.98  --include_path                          ""
% 2.52/0.98  --clausifier                            res/vclausify_rel
% 2.52/0.98  --clausifier_options                    --mode clausify
% 2.52/0.98  --stdin                                 false
% 2.52/0.98  --stats_out                             all
% 2.52/0.98  
% 2.52/0.98  ------ General Options
% 2.52/0.98  
% 2.52/0.98  --fof                                   false
% 2.52/0.98  --time_out_real                         305.
% 2.52/0.98  --time_out_virtual                      -1.
% 2.52/0.98  --symbol_type_check                     false
% 2.52/0.98  --clausify_out                          false
% 2.52/0.98  --sig_cnt_out                           false
% 2.52/0.98  --trig_cnt_out                          false
% 2.52/0.98  --trig_cnt_out_tolerance                1.
% 2.52/0.98  --trig_cnt_out_sk_spl                   false
% 2.52/0.98  --abstr_cl_out                          false
% 2.52/0.98  
% 2.52/0.98  ------ Global Options
% 2.52/0.98  
% 2.52/0.98  --schedule                              default
% 2.52/0.98  --add_important_lit                     false
% 2.52/0.98  --prop_solver_per_cl                    1000
% 2.52/0.98  --min_unsat_core                        false
% 2.52/0.98  --soft_assumptions                      false
% 2.52/0.98  --soft_lemma_size                       3
% 2.52/0.98  --prop_impl_unit_size                   0
% 2.52/0.98  --prop_impl_unit                        []
% 2.52/0.98  --share_sel_clauses                     true
% 2.52/0.98  --reset_solvers                         false
% 2.52/0.98  --bc_imp_inh                            [conj_cone]
% 2.52/0.98  --conj_cone_tolerance                   3.
% 2.52/0.98  --extra_neg_conj                        none
% 2.52/0.98  --large_theory_mode                     true
% 2.52/0.98  --prolific_symb_bound                   200
% 2.52/0.98  --lt_threshold                          2000
% 2.52/0.98  --clause_weak_htbl                      true
% 2.52/0.98  --gc_record_bc_elim                     false
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing Options
% 2.52/0.98  
% 2.52/0.98  --preprocessing_flag                    true
% 2.52/0.98  --time_out_prep_mult                    0.1
% 2.52/0.98  --splitting_mode                        input
% 2.52/0.98  --splitting_grd                         true
% 2.52/0.98  --splitting_cvd                         false
% 2.52/0.98  --splitting_cvd_svl                     false
% 2.52/0.98  --splitting_nvd                         32
% 2.52/0.98  --sub_typing                            true
% 2.52/0.98  --prep_gs_sim                           true
% 2.52/0.98  --prep_unflatten                        true
% 2.52/0.98  --prep_res_sim                          true
% 2.52/0.98  --prep_upred                            true
% 2.52/0.98  --prep_sem_filter                       exhaustive
% 2.52/0.98  --prep_sem_filter_out                   false
% 2.52/0.98  --pred_elim                             true
% 2.52/0.98  --res_sim_input                         true
% 2.52/0.98  --eq_ax_congr_red                       true
% 2.52/0.98  --pure_diseq_elim                       true
% 2.52/0.98  --brand_transform                       false
% 2.52/0.98  --non_eq_to_eq                          false
% 2.52/0.98  --prep_def_merge                        true
% 2.52/0.98  --prep_def_merge_prop_impl              false
% 2.52/0.98  --prep_def_merge_mbd                    true
% 2.52/0.98  --prep_def_merge_tr_red                 false
% 2.52/0.98  --prep_def_merge_tr_cl                  false
% 2.52/0.98  --smt_preprocessing                     true
% 2.52/0.98  --smt_ac_axioms                         fast
% 2.52/0.98  --preprocessed_out                      false
% 2.52/0.98  --preprocessed_stats                    false
% 2.52/0.98  
% 2.52/0.98  ------ Abstraction refinement Options
% 2.52/0.98  
% 2.52/0.98  --abstr_ref                             []
% 2.52/0.98  --abstr_ref_prep                        false
% 2.52/0.98  --abstr_ref_until_sat                   false
% 2.52/0.98  --abstr_ref_sig_restrict                funpre
% 2.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.98  --abstr_ref_under                       []
% 2.52/0.98  
% 2.52/0.98  ------ SAT Options
% 2.52/0.98  
% 2.52/0.98  --sat_mode                              false
% 2.52/0.98  --sat_fm_restart_options                ""
% 2.52/0.98  --sat_gr_def                            false
% 2.52/0.98  --sat_epr_types                         true
% 2.52/0.98  --sat_non_cyclic_types                  false
% 2.52/0.98  --sat_finite_models                     false
% 2.52/0.98  --sat_fm_lemmas                         false
% 2.52/0.98  --sat_fm_prep                           false
% 2.52/0.98  --sat_fm_uc_incr                        true
% 2.52/0.98  --sat_out_model                         small
% 2.52/0.98  --sat_out_clauses                       false
% 2.52/0.98  
% 2.52/0.98  ------ QBF Options
% 2.52/0.98  
% 2.52/0.98  --qbf_mode                              false
% 2.52/0.98  --qbf_elim_univ                         false
% 2.52/0.98  --qbf_dom_inst                          none
% 2.52/0.98  --qbf_dom_pre_inst                      false
% 2.52/0.98  --qbf_sk_in                             false
% 2.52/0.98  --qbf_pred_elim                         true
% 2.52/0.98  --qbf_split                             512
% 2.52/0.98  
% 2.52/0.98  ------ BMC1 Options
% 2.52/0.98  
% 2.52/0.98  --bmc1_incremental                      false
% 2.52/0.98  --bmc1_axioms                           reachable_all
% 2.52/0.98  --bmc1_min_bound                        0
% 2.52/0.98  --bmc1_max_bound                        -1
% 2.52/0.98  --bmc1_max_bound_default                -1
% 2.52/0.98  --bmc1_symbol_reachability              true
% 2.52/0.98  --bmc1_property_lemmas                  false
% 2.52/0.98  --bmc1_k_induction                      false
% 2.52/0.98  --bmc1_non_equiv_states                 false
% 2.52/0.98  --bmc1_deadlock                         false
% 2.52/0.98  --bmc1_ucm                              false
% 2.52/0.98  --bmc1_add_unsat_core                   none
% 2.52/0.98  --bmc1_unsat_core_children              false
% 2.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.98  --bmc1_out_stat                         full
% 2.52/0.98  --bmc1_ground_init                      false
% 2.52/0.98  --bmc1_pre_inst_next_state              false
% 2.52/0.98  --bmc1_pre_inst_state                   false
% 2.52/0.98  --bmc1_pre_inst_reach_state             false
% 2.52/0.98  --bmc1_out_unsat_core                   false
% 2.52/0.98  --bmc1_aig_witness_out                  false
% 2.52/0.98  --bmc1_verbose                          false
% 2.52/0.98  --bmc1_dump_clauses_tptp                false
% 2.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.98  --bmc1_dump_file                        -
% 2.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.98  --bmc1_ucm_extend_mode                  1
% 2.52/0.98  --bmc1_ucm_init_mode                    2
% 2.52/0.98  --bmc1_ucm_cone_mode                    none
% 2.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.98  --bmc1_ucm_relax_model                  4
% 2.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.98  --bmc1_ucm_layered_model                none
% 2.52/0.98  --bmc1_ucm_max_lemma_size               10
% 2.52/0.98  
% 2.52/0.98  ------ AIG Options
% 2.52/0.98  
% 2.52/0.98  --aig_mode                              false
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation Options
% 2.52/0.98  
% 2.52/0.98  --instantiation_flag                    true
% 2.52/0.98  --inst_sos_flag                         false
% 2.52/0.98  --inst_sos_phase                        true
% 2.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel_side                     none
% 2.52/0.98  --inst_solver_per_active                1400
% 2.52/0.98  --inst_solver_calls_frac                1.
% 2.52/0.98  --inst_passive_queue_type               priority_queues
% 2.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       false
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    passive
% 2.52/0.99  --sup_prop_simpl_new                    true
% 2.52/0.99  --sup_prop_simpl_given                  true
% 2.52/0.99  --sup_fun_splitting                     false
% 2.52/0.99  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ Proving...
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS status Theorem for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  fof(f12,conjecture,(
% 2.52/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f13,negated_conjecture,(
% 2.52/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.52/0.99    inference(negated_conjecture,[],[f12])).
% 2.52/0.99  
% 2.52/0.99  fof(f26,plain,(
% 2.52/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.52/0.99    inference(ennf_transformation,[],[f13])).
% 2.52/0.99  
% 2.52/0.99  fof(f27,plain,(
% 2.52/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.52/0.99    inference(flattening,[],[f26])).
% 2.52/0.99  
% 2.52/0.99  fof(f39,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f38,plain,(
% 2.52/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f40,plain,(
% 2.52/0.99    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f39,f38])).
% 2.52/0.99  
% 2.52/0.99  fof(f67,plain,(
% 2.52/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f11,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f24,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f11])).
% 2.52/0.99  
% 2.52/0.99  fof(f25,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(flattening,[],[f24])).
% 2.52/0.99  
% 2.52/0.99  fof(f37,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(nnf_transformation,[],[f25])).
% 2.52/0.99  
% 2.52/0.99  fof(f57,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f37])).
% 2.52/0.99  
% 2.52/0.99  fof(f68,plain,(
% 2.52/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f9,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f21,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f9])).
% 2.52/0.99  
% 2.52/0.99  fof(f54,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f21])).
% 2.52/0.99  
% 2.52/0.99  fof(f64,plain,(
% 2.52/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f65,plain,(
% 2.52/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f6,axiom,(
% 2.52/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f17,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f6])).
% 2.52/0.99  
% 2.52/0.99  fof(f18,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.52/0.99    inference(flattening,[],[f17])).
% 2.52/0.99  
% 2.52/0.99  fof(f34,plain,(
% 2.52/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f35,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).
% 2.52/0.99  
% 2.52/0.99  fof(f50,plain,(
% 2.52/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f35])).
% 2.52/0.99  
% 2.52/0.99  fof(f66,plain,(
% 2.52/0.99    v1_funct_1(sK5)),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f8,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f20,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f8])).
% 2.52/0.99  
% 2.52/0.99  fof(f53,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f20])).
% 2.52/0.99  
% 2.52/0.99  fof(f63,plain,(
% 2.52/0.99    v1_funct_1(sK4)),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f10,axiom,(
% 2.52/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f22,plain,(
% 2.52/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.52/0.99    inference(ennf_transformation,[],[f10])).
% 2.52/0.99  
% 2.52/0.99  fof(f23,plain,(
% 2.52/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(flattening,[],[f22])).
% 2.52/0.99  
% 2.52/0.99  fof(f36,plain,(
% 2.52/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(nnf_transformation,[],[f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f56,plain,(
% 2.52/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f36])).
% 2.52/0.99  
% 2.52/0.99  fof(f73,plain,(
% 2.52/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(equality_resolution,[],[f56])).
% 2.52/0.99  
% 2.52/0.99  fof(f70,plain,(
% 2.52/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f69,plain,(
% 2.52/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f51,plain,(
% 2.52/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f35])).
% 2.52/0.99  
% 2.52/0.99  fof(f1,axiom,(
% 2.52/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f14,plain,(
% 2.52/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f1])).
% 2.52/0.99  
% 2.52/0.99  fof(f28,plain,(
% 2.52/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/0.99    inference(nnf_transformation,[],[f14])).
% 2.52/0.99  
% 2.52/0.99  fof(f29,plain,(
% 2.52/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/0.99    inference(rectify,[],[f28])).
% 2.52/0.99  
% 2.52/0.99  fof(f30,plain,(
% 2.52/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f31,plain,(
% 2.52/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.52/0.99  
% 2.52/0.99  fof(f42,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f31])).
% 2.52/0.99  
% 2.52/0.99  fof(f5,axiom,(
% 2.52/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f16,plain,(
% 2.52/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f5])).
% 2.52/0.99  
% 2.52/0.99  fof(f49,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f16])).
% 2.52/0.99  
% 2.52/0.99  fof(f43,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f31])).
% 2.52/0.99  
% 2.52/0.99  fof(f61,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f37])).
% 2.52/0.99  
% 2.52/0.99  fof(f76,plain,(
% 2.52/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.52/0.99    inference(equality_resolution,[],[f61])).
% 2.52/0.99  
% 2.52/0.99  fof(f4,axiom,(
% 2.52/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f32,plain,(
% 2.52/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.52/0.99    inference(nnf_transformation,[],[f4])).
% 2.52/0.99  
% 2.52/0.99  fof(f33,plain,(
% 2.52/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.52/0.99    inference(flattening,[],[f32])).
% 2.52/0.99  
% 2.52/0.99  fof(f48,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f71,plain,(
% 2.52/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.52/0.99    inference(equality_resolution,[],[f48])).
% 2.52/0.99  
% 2.52/0.99  fof(f47,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f72,plain,(
% 2.52/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.52/0.99    inference(equality_resolution,[],[f47])).
% 2.52/0.99  
% 2.52/0.99  fof(f3,axiom,(
% 2.52/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f15,plain,(
% 2.52/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.52/0.99    inference(ennf_transformation,[],[f3])).
% 2.52/0.99  
% 2.52/0.99  fof(f45,plain,(
% 2.52/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f15])).
% 2.52/0.99  
% 2.52/0.99  cnf(c_25,negated_conjecture,
% 2.52/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.52/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_21,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.52/0.99      | k1_xboole_0 = X2 ),
% 2.52/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_24,negated_conjecture,
% 2.52/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_450,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != X0
% 2.52/0.99      | k1_xboole_0 = X2 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_451,plain,
% 2.52/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 2.52/0.99      | k1_relset_1(X0,X1,sK5) = X0
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_450]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_796,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,sK5) = X0
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != sK5
% 2.52/0.99      | sK3 != X1
% 2.52/0.99      | sK2 != X0
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_451]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_797,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = sK3 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_796]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1442,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.52/0.99      inference(equality_resolution_simp,[status(thm)],[c_797]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_13,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_486,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != X2 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_487,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_486]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1614,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.52/0.99      inference(equality_resolution,[status(thm)],[c_487]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2484,plain,
% 2.52/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_1442,c_1614]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_28,negated_conjecture,
% 2.52/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.52/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_27,negated_conjecture,
% 2.52/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_507,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != X0
% 2.52/0.99      | k1_xboole_0 = X2 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_508,plain,
% 2.52/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.52/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_881,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != sK4
% 2.52/0.99      | sK3 != X1
% 2.52/0.99      | sK2 != X0
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_508]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_882,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = sK3 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_881]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1437,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.52/0.99      inference(equality_resolution_simp,[status(thm)],[c_882]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_543,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != X2 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_544,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1617,plain,
% 2.52/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.52/0.99      inference(equality_resolution,[status(thm)],[c_544]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2360,plain,
% 2.52/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_1437,c_1617]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_10,plain,
% 2.52/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.52/0.99      | ~ v1_relat_1(X1)
% 2.52/0.99      | ~ v1_relat_1(X0)
% 2.52/0.99      | ~ v1_funct_1(X1)
% 2.52/0.99      | ~ v1_funct_1(X0)
% 2.52/0.99      | X1 = X0
% 2.52/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1370,plain,
% 2.52/0.99      ( X0 = X1
% 2.52/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.52/0.99      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.52/0.99      | v1_relat_1(X1) != iProver_top
% 2.52/0.99      | v1_relat_1(X0) != iProver_top
% 2.52/0.99      | v1_funct_1(X0) != iProver_top
% 2.52/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2595,plain,
% 2.52/0.99      ( k1_relat_1(X0) != sK2
% 2.52/0.99      | sK5 = X0
% 2.52/0.99      | sK3 = k1_xboole_0
% 2.52/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.52/0.99      | v1_relat_1(X0) != iProver_top
% 2.52/0.99      | v1_relat_1(sK5) != iProver_top
% 2.52/0.99      | v1_funct_1(X0) != iProver_top
% 2.52/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2484,c_1370]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_26,negated_conjecture,
% 2.52/0.99      ( v1_funct_1(sK5) ),
% 2.52/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_33,plain,
% 2.52/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1062,plain,( X0 = X0 ),theory(equality) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1601,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1062]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_12,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | v1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_495,plain,
% 2.52/0.99      ( v1_relat_1(X0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != X0 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_496,plain,
% 2.52/0.99      ( v1_relat_1(sK5)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_495]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1605,plain,
% 2.52/0.99      ( v1_relat_1(sK5)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_496]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1606,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1605]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3278,plain,
% 2.52/0.99      ( v1_funct_1(X0) != iProver_top
% 2.52/0.99      | k1_relat_1(X0) != sK2
% 2.52/0.99      | sK5 = X0
% 2.52/0.99      | sK3 = k1_xboole_0
% 2.52/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_2595,c_33,c_1601,c_1606]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3279,plain,
% 2.52/0.99      ( k1_relat_1(X0) != sK2
% 2.52/0.99      | sK5 = X0
% 2.52/0.99      | sK3 = k1_xboole_0
% 2.52/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.52/0.99      | v1_relat_1(X0) != iProver_top
% 2.52/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_3278]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3291,plain,
% 2.52/0.99      ( sK5 = sK4
% 2.52/0.99      | sK3 = k1_xboole_0
% 2.52/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.52/0.99      | v1_relat_1(sK4) != iProver_top
% 2.52/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2360,c_3279]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_29,negated_conjecture,
% 2.52/0.99      ( v1_funct_1(sK4) ),
% 2.52/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_30,plain,
% 2.52/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_14,plain,
% 2.52/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.52/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_22,negated_conjecture,
% 2.52/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.52/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_303,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | sK5 != X0
% 2.52/0.99      | sK4 != X0
% 2.52/0.99      | sK3 != X2
% 2.52/0.99      | sK2 != X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_304,plain,
% 2.52/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.52/0.99      | sK4 != sK5 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_303]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_552,plain,
% 2.52/0.99      ( v1_relat_1(X0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != X0 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_553,plain,
% 2.52/0.99      ( v1_relat_1(sK4)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_552]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1604,plain,
% 2.52/0.99      ( v1_relat_1(sK4)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_553]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1608,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1604]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2074,plain,
% 2.52/0.99      ( sK4 = sK4 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1062]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1063,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1906,plain,
% 2.52/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2073,plain,
% 2.52/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1906]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2786,plain,
% 2.52/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3318,plain,
% 2.52/0.99      ( sK3 = k1_xboole_0
% 2.52/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_3291,c_30,c_24,c_304,c_1601,c_1608,c_2074,c_2786]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3324,plain,
% 2.52/0.99      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2360,c_3318]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_23,negated_conjecture,
% 2.52/0.99      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1368,plain,
% 2.52/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.52/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3351,plain,
% 2.52/0.99      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.52/0.99      | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3324,c_1368]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_9,plain,
% 2.52/0.99      ( ~ v1_relat_1(X0)
% 2.52/0.99      | ~ v1_relat_1(X1)
% 2.52/0.99      | ~ v1_funct_1(X0)
% 2.52/0.99      | ~ v1_funct_1(X1)
% 2.52/0.99      | X0 = X1
% 2.52/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.52/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1371,plain,
% 2.52/0.99      ( X0 = X1
% 2.52/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.52/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.52/0.99      | v1_relat_1(X0) != iProver_top
% 2.52/0.99      | v1_relat_1(X1) != iProver_top
% 2.52/0.99      | v1_funct_1(X1) != iProver_top
% 2.52/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3402,plain,
% 2.52/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.52/0.99      | sK5 = sK4
% 2.52/0.99      | sK3 = k1_xboole_0
% 2.52/0.99      | v1_relat_1(sK5) != iProver_top
% 2.52/0.99      | v1_relat_1(sK4) != iProver_top
% 2.52/0.99      | v1_funct_1(sK5) != iProver_top
% 2.52/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3351,c_1371]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3403,plain,
% 2.52/0.99      ( ~ v1_relat_1(sK5)
% 2.52/0.99      | ~ v1_relat_1(sK4)
% 2.52/0.99      | ~ v1_funct_1(sK5)
% 2.52/0.99      | ~ v1_funct_1(sK4)
% 2.52/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.52/0.99      | sK5 = sK4
% 2.52/0.99      | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3402]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3405,plain,
% 2.52/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_3402,c_29,c_26,c_24,c_304,c_1601,c_1605,c_1604,c_2074,
% 2.52/0.99                 c_2786,c_3403]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3409,plain,
% 2.52/0.99      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2484,c_3405]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3457,plain,
% 2.52/0.99      ( sK3 = k1_xboole_0 ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_3409,c_2360]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1,plain,
% 2.52/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1375,plain,
% 2.52/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.52/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_8,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.99      | ~ r2_hidden(X2,X0)
% 2.52/0.99      | r2_hidden(X2,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_420,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,X1)
% 2.52/0.99      | r2_hidden(X0,X2)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
% 2.52/0.99      | sK5 != X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_421,plain,
% 2.52/0.99      ( r2_hidden(X0,X1)
% 2.52/0.99      | ~ r2_hidden(X0,sK5)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1365,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 2.52/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.52/0.99      | r2_hidden(X1,sK5) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2356,plain,
% 2.52/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.52/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 2.52/0.99      inference(equality_resolution,[status(thm)],[c_1365]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_0,plain,
% 2.52/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1376,plain,
% 2.52/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.52/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2795,plain,
% 2.52/0.99      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK5) != iProver_top
% 2.52/0.99      | r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2356,c_1376]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3015,plain,
% 2.52/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1375,c_2795]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3464,plain,
% 2.52/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3457,c_3015]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_17,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.52/0.99      | k1_xboole_0 = X1
% 2.52/0.99      | k1_xboole_0 = X0 ),
% 2.52/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_616,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != X0
% 2.52/0.99      | k1_xboole_0 = X0
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_617,plain,
% 2.52/0.99      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = X0
% 2.52/0.99      | k1_xboole_0 = sK4 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_616]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_896,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 != sK4
% 2.52/0.99      | sK4 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | sK2 != X0
% 2.52/0.99      | k1_xboole_0 = X0 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_617]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_897,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK4 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | k1_xboole_0 = sK2 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_896]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_5,plain,
% 2.52/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.52/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1473,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK4 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_897,c_5]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_598,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != X0
% 2.52/0.99      | k1_xboole_0 = X0
% 2.52/0.99      | k1_xboole_0 = X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_599,plain,
% 2.52/0.99      ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | k1_xboole_0 = X0
% 2.52/0.99      | k1_xboole_0 = sK5 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_598]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_821,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 != sK5
% 2.52/0.99      | sK5 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | sK2 != X0
% 2.52/0.99      | k1_xboole_0 = X0 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_599]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_822,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.52/0.99      | sK5 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | k1_xboole_0 = sK2 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_821]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1482,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK5 = k1_xboole_0
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_822,c_5]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1628,plain,
% 2.52/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1629,plain,
% 2.52/0.99      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1628]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2526,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK3 != k1_xboole_0
% 2.52/0.99      | sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_1473,c_24,c_304,c_1482,c_1629]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3473,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK2 = k1_xboole_0
% 2.52/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3457,c_2526]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3552,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(equality_resolution_simp,[status(thm)],[c_3473]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3555,plain,
% 2.52/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.52/0.99      | sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3552,c_5]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3556,plain,
% 2.52/0.99      ( sK2 = k1_xboole_0 ),
% 2.52/0.99      inference(equality_resolution_simp,[status(thm)],[c_3555]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3628,plain,
% 2.52/0.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.52/0.99      inference(light_normalisation,[status(thm)],[c_3464,c_3556]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_6,plain,
% 2.52/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.52/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3630,plain,
% 2.52/0.99      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3628,c_6]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_435,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,X1)
% 2.52/0.99      | r2_hidden(X0,X2)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
% 2.52/0.99      | sK4 != X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_436,plain,
% 2.52/0.99      ( r2_hidden(X0,X1)
% 2.52/0.99      | ~ r2_hidden(X0,sK4)
% 2.52/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1364,plain,
% 2.52/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 2.52/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.52/0.99      | r2_hidden(X1,sK4) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2298,plain,
% 2.52/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.52/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.52/0.99      inference(equality_resolution,[status(thm)],[c_1364]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2680,plain,
% 2.52/0.99      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK2,sK3)),sK4) != iProver_top
% 2.52/0.99      | r1_tarski(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_2298,c_1376]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2964,plain,
% 2.52/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1375,c_2680]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3465,plain,
% 2.52/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3457,c_2964]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3624,plain,
% 2.52/0.99      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.52/0.99      inference(light_normalisation,[status(thm)],[c_3465,c_3556]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3626,plain,
% 2.52/0.99      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3624,c_6]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2421,plain,
% 2.52/0.99      ( sK5 = sK5 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1062]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1854,plain,
% 2.52/0.99      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2420,plain,
% 2.52/0.99      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1854]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2422,plain,
% 2.52/0.99      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_2420]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2075,plain,
% 2.52/0.99      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4,plain,
% 2.52/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.52/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1695,plain,
% 2.52/0.99      ( ~ r1_tarski(sK4,k1_xboole_0) | k1_xboole_0 = sK4 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1698,plain,
% 2.52/0.99      ( k1_xboole_0 = sK4 | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1695]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1674,plain,
% 2.52/0.99      ( ~ r1_tarski(sK5,k1_xboole_0) | k1_xboole_0 = sK5 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1677,plain,
% 2.52/0.99      ( k1_xboole_0 = sK5 | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1674]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1632,plain,
% 2.52/0.99      ( sK5 != X0 | sK5 = sK4 | sK4 != X0 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1063]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1633,plain,
% 2.52/0.99      ( sK5 = sK4 | sK5 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1632]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(contradiction,plain,
% 2.52/0.99      ( $false ),
% 2.52/0.99      inference(minisat,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_3630,c_3626,c_2786,c_2421,c_2422,c_2074,c_2075,c_1698,
% 2.52/0.99                 c_1677,c_1633,c_304,c_24]) ).
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  ------                               Statistics
% 2.52/0.99  
% 2.52/0.99  ------ General
% 2.52/0.99  
% 2.52/0.99  abstr_ref_over_cycles:                  0
% 2.52/0.99  abstr_ref_under_cycles:                 0
% 2.52/0.99  gc_basic_clause_elim:                   0
% 2.52/0.99  forced_gc_time:                         0
% 2.52/0.99  parsing_time:                           0.008
% 2.52/0.99  unif_index_cands_time:                  0.
% 2.52/0.99  unif_index_add_time:                    0.
% 2.52/0.99  orderings_time:                         0.
% 2.52/0.99  out_proof_time:                         0.01
% 2.52/0.99  total_time:                             0.161
% 2.52/0.99  num_of_symbols:                         50
% 2.52/0.99  num_of_terms:                           2344
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing
% 2.52/0.99  
% 2.52/0.99  num_of_splits:                          0
% 2.52/0.99  num_of_split_atoms:                     0
% 2.52/0.99  num_of_reused_defs:                     0
% 2.52/0.99  num_eq_ax_congr_red:                    12
% 2.52/0.99  num_of_sem_filtered_clauses:            1
% 2.52/0.99  num_of_subtypes:                        0
% 2.52/0.99  monotx_restored_types:                  0
% 2.52/0.99  sat_num_of_epr_types:                   0
% 2.52/0.99  sat_num_of_non_cyclic_types:            0
% 2.52/0.99  sat_guarded_non_collapsed_types:        0
% 2.52/0.99  num_pure_diseq_elim:                    0
% 2.52/0.99  simp_replaced_by:                       0
% 2.52/0.99  res_preprocessed:                       115
% 2.52/0.99  prep_upred:                             0
% 2.52/0.99  prep_unflattend:                        115
% 2.52/0.99  smt_new_axioms:                         0
% 2.52/0.99  pred_elim_cands:                        7
% 2.52/0.99  pred_elim:                              3
% 2.52/0.99  pred_elim_cl:                           -1
% 2.52/0.99  pred_elim_cycles:                       5
% 2.52/0.99  merged_defs:                            0
% 2.52/0.99  merged_defs_ncl:                        0
% 2.52/0.99  bin_hyper_res:                          0
% 2.52/0.99  prep_cycles:                            3
% 2.52/0.99  pred_elim_time:                         0.016
% 2.52/0.99  splitting_time:                         0.
% 2.52/0.99  sem_filter_time:                        0.
% 2.52/0.99  monotx_time:                            0.
% 2.52/0.99  subtype_inf_time:                       0.
% 2.52/0.99  
% 2.52/0.99  ------ Problem properties
% 2.52/0.99  
% 2.52/0.99  clauses:                                31
% 2.52/0.99  conjectures:                            3
% 2.52/0.99  epr:                                    7
% 2.52/0.99  horn:                                   22
% 2.52/0.99  ground:                                 9
% 2.52/0.99  unary:                                  6
% 2.52/0.99  binary:                                 9
% 2.52/0.99  lits:                                   88
% 2.52/0.99  lits_eq:                                59
% 2.52/0.99  fd_pure:                                0
% 2.52/0.99  fd_pseudo:                              0
% 2.52/0.99  fd_cond:                                2
% 2.52/0.99  fd_pseudo_cond:                         2
% 2.52/0.99  ac_symbols:                             0
% 2.52/0.99  
% 2.52/0.99  ------ Propositional Solver
% 2.52/0.99  
% 2.52/0.99  prop_solver_calls:                      23
% 2.52/0.99  prop_fast_solver_calls:                 975
% 2.52/0.99  smt_solver_calls:                       0
% 2.52/0.99  smt_fast_solver_calls:                  0
% 2.52/0.99  prop_num_of_clauses:                    930
% 2.52/0.99  prop_preprocess_simplified:             3694
% 2.52/0.99  prop_fo_subsumed:                       28
% 2.52/0.99  prop_solver_time:                       0.
% 2.52/0.99  smt_solver_time:                        0.
% 2.52/0.99  smt_fast_solver_time:                   0.
% 2.52/0.99  prop_fast_solver_time:                  0.
% 2.52/0.99  prop_unsat_core_time:                   0.
% 2.52/0.99  
% 2.52/0.99  ------ QBF
% 2.52/0.99  
% 2.52/0.99  qbf_q_res:                              0
% 2.52/0.99  qbf_num_tautologies:                    0
% 2.52/0.99  qbf_prep_cycles:                        0
% 2.52/0.99  
% 2.52/0.99  ------ BMC1
% 2.52/0.99  
% 2.52/0.99  bmc1_current_bound:                     -1
% 2.52/0.99  bmc1_last_solved_bound:                 -1
% 2.52/0.99  bmc1_unsat_core_size:                   -1
% 2.52/0.99  bmc1_unsat_core_parents_size:           -1
% 2.52/0.99  bmc1_merge_next_fun:                    0
% 2.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation
% 2.52/0.99  
% 2.52/0.99  inst_num_of_clauses:                    304
% 2.52/0.99  inst_num_in_passive:                    48
% 2.52/0.99  inst_num_in_active:                     196
% 2.52/0.99  inst_num_in_unprocessed:                60
% 2.52/0.99  inst_num_of_loops:                      280
% 2.52/0.99  inst_num_of_learning_restarts:          0
% 2.52/0.99  inst_num_moves_active_passive:          81
% 2.52/0.99  inst_lit_activity:                      0
% 2.52/0.99  inst_lit_activity_moves:                0
% 2.52/0.99  inst_num_tautologies:                   0
% 2.52/0.99  inst_num_prop_implied:                  0
% 2.52/0.99  inst_num_existing_simplified:           0
% 2.52/0.99  inst_num_eq_res_simplified:             0
% 2.52/0.99  inst_num_child_elim:                    0
% 2.52/0.99  inst_num_of_dismatching_blockings:      48
% 2.52/0.99  inst_num_of_non_proper_insts:           505
% 2.52/0.99  inst_num_of_duplicates:                 0
% 2.52/0.99  inst_inst_num_from_inst_to_res:         0
% 2.52/0.99  inst_dismatching_checking_time:         0.
% 2.52/0.99  
% 2.52/0.99  ------ Resolution
% 2.52/0.99  
% 2.52/0.99  res_num_of_clauses:                     0
% 2.52/0.99  res_num_in_passive:                     0
% 2.52/0.99  res_num_in_active:                      0
% 2.52/0.99  res_num_of_loops:                       118
% 2.52/0.99  res_forward_subset_subsumed:            32
% 2.52/0.99  res_backward_subset_subsumed:           2
% 2.52/0.99  res_forward_subsumed:                   7
% 2.52/0.99  res_backward_subsumed:                  5
% 2.52/0.99  res_forward_subsumption_resolution:     0
% 2.52/0.99  res_backward_subsumption_resolution:    0
% 2.52/0.99  res_clause_to_clause_subsumption:       279
% 2.52/0.99  res_orphan_elimination:                 0
% 2.52/0.99  res_tautology_del:                      67
% 2.52/0.99  res_num_eq_res_simplified:              2
% 2.52/0.99  res_num_sel_changes:                    0
% 2.52/0.99  res_moves_from_active_to_pass:          0
% 2.52/0.99  
% 2.52/0.99  ------ Superposition
% 2.52/0.99  
% 2.52/0.99  sup_time_total:                         0.
% 2.52/0.99  sup_time_generating:                    0.
% 2.52/0.99  sup_time_sim_full:                      0.
% 2.52/0.99  sup_time_sim_immed:                     0.
% 2.52/0.99  
% 2.52/0.99  sup_num_of_clauses:                     54
% 2.52/0.99  sup_num_in_active:                      24
% 2.52/0.99  sup_num_in_passive:                     30
% 2.52/0.99  sup_num_of_loops:                       54
% 2.52/0.99  sup_fw_superposition:                   21
% 2.52/0.99  sup_bw_superposition:                   22
% 2.52/0.99  sup_immediate_simplified:               48
% 2.52/0.99  sup_given_eliminated:                   0
% 2.52/0.99  comparisons_done:                       0
% 2.52/0.99  comparisons_avoided:                    12
% 2.52/0.99  
% 2.52/0.99  ------ Simplifications
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  sim_fw_subset_subsumed:                 5
% 2.52/0.99  sim_bw_subset_subsumed:                 6
% 2.52/0.99  sim_fw_subsumed:                        0
% 2.52/0.99  sim_bw_subsumed:                        2
% 2.52/0.99  sim_fw_subsumption_res:                 0
% 2.52/0.99  sim_bw_subsumption_res:                 0
% 2.52/0.99  sim_tautology_del:                      0
% 2.52/0.99  sim_eq_tautology_del:                   8
% 2.52/0.99  sim_eq_res_simp:                        12
% 2.52/0.99  sim_fw_demodulated:                     31
% 2.52/0.99  sim_bw_demodulated:                     36
% 2.52/0.99  sim_light_normalised:                   14
% 2.52/0.99  sim_joinable_taut:                      0
% 2.52/0.99  sim_joinable_simp:                      0
% 2.52/0.99  sim_ac_normalised:                      0
% 2.52/0.99  sim_smt_subsumption:                    0
% 2.52/0.99  
%------------------------------------------------------------------------------
