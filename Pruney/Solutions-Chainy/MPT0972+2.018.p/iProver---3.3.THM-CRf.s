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
% DateTime   : Thu Dec  3 12:01:11 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  197 (7413 expanded)
%              Number of clauses        :  131 (2191 expanded)
%              Number of leaves         :   17 (1799 expanded)
%              Depth                    :   30
%              Number of atoms          :  648 (47881 expanded)
%              Number of equality atoms :  335 (11556 expanded)
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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38])).

fof(f68,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f71,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f70,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_488,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_25])).

cnf(c_2115,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2117,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2955,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2115,c_2117])).

cnf(c_3054,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_488,c_2955])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_497,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_499,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_28])).

cnf(c_2113,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2956,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2113,c_2117])).

cnf(c_3057,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_499,c_2956])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2120,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3371,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_2120])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2319,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_3722,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3371,c_34,c_36,c_2319])).

cnf(c_3723,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3722])).

cnf(c_3735,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_3723])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_2321,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2322,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2416,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2621,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2622,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1553,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2347,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_2985,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_3748,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3735,c_31,c_33,c_25,c_403,c_2322,c_2621,c_2622,c_2985])).

cnf(c_3754,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_3748])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2116,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3861,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3754,c_2116])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2121,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3886,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3861,c_2121])).

cnf(c_3887,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3886])).

cnf(c_3945,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_30,c_28,c_27,c_25,c_403,c_2318,c_2321,c_2621,c_2622,c_2985,c_3887])).

cnf(c_3949,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3054,c_3945])).

cnf(c_3950,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3949,c_3057])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK3 != k1_xboole_0
    | sK2 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_2109,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_3962,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2109])).

cnf(c_3991,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3962])).

cnf(c_3970,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2113])).

cnf(c_3995,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3991,c_3970])).

cnf(c_2426,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_2984,plain,
    ( sK5 != X0
    | sK5 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_2986,plain,
    ( sK5 = sK4
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2984])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK3 != k1_xboole_0
    | sK2 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_424,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_2110,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK2
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_3961,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2110])).

cnf(c_3998,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3961])).

cnf(c_3969,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2115])).

cnf(c_4002,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3998,c_3969])).

cnf(c_4736,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3995,c_25,c_403,c_2621,c_2622,c_2986,c_2985,c_4002])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2638,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2122])).

cnf(c_3964,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2638])).

cnf(c_4740,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4736,c_3964])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2128,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_232])).

cnf(c_2111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_2900,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_2111])).

cnf(c_5705,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4740,c_2900])).

cnf(c_5724,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5705])).

cnf(c_2637,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_2122])).

cnf(c_3965,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3950,c_2637])).

cnf(c_4739,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4736,c_3965])).

cnf(c_5680,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_2900])).

cnf(c_5699,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5680])).

cnf(c_2124,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3266,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_2118])).

cnf(c_5290,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_3266])).

cnf(c_5297,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5290])).

cnf(c_4058,plain,
    ( ~ r2_hidden(sK0(X0,sK4),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_4059,plain,
    ( r2_hidden(sK0(X0,sK4),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4058])).

cnf(c_4061,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4059])).

cnf(c_3147,plain,
    ( ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_3148,plain,
    ( r2_hidden(sK0(X0,sK5),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3147])).

cnf(c_3150,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_2651,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2652,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_2654,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2652])).

cnf(c_2606,plain,
    ( r2_hidden(sK0(X0,sK4),X0)
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2617,plain,
    ( r2_hidden(sK0(X0,sK4),X0) = iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_2619,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_2585,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2596,plain,
    ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_2598,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2596])).

cnf(c_2500,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2501,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2500])).

cnf(c_2503,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_2348,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_87,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_89,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5724,c_5699,c_5297,c_4061,c_3150,c_2654,c_2619,c_2598,c_2503,c_2348,c_403,c_94,c_89,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:35:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.98/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/0.97  
% 2.98/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.97  
% 2.98/0.97  ------  iProver source info
% 2.98/0.97  
% 2.98/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.97  git: non_committed_changes: false
% 2.98/0.97  git: last_make_outside_of_git: false
% 2.98/0.97  
% 2.98/0.97  ------ 
% 2.98/0.97  
% 2.98/0.97  ------ Input Options
% 2.98/0.97  
% 2.98/0.97  --out_options                           all
% 2.98/0.97  --tptp_safe_out                         true
% 2.98/0.97  --problem_path                          ""
% 2.98/0.97  --include_path                          ""
% 2.98/0.97  --clausifier                            res/vclausify_rel
% 2.98/0.97  --clausifier_options                    --mode clausify
% 2.98/0.97  --stdin                                 false
% 2.98/0.97  --stats_out                             all
% 2.98/0.97  
% 2.98/0.97  ------ General Options
% 2.98/0.97  
% 2.98/0.97  --fof                                   false
% 2.98/0.97  --time_out_real                         305.
% 2.98/0.97  --time_out_virtual                      -1.
% 2.98/0.97  --symbol_type_check                     false
% 2.98/0.97  --clausify_out                          false
% 2.98/0.97  --sig_cnt_out                           false
% 2.98/0.97  --trig_cnt_out                          false
% 2.98/0.97  --trig_cnt_out_tolerance                1.
% 2.98/0.97  --trig_cnt_out_sk_spl                   false
% 2.98/0.97  --abstr_cl_out                          false
% 2.98/0.97  
% 2.98/0.97  ------ Global Options
% 2.98/0.97  
% 2.98/0.97  --schedule                              default
% 2.98/0.97  --add_important_lit                     false
% 2.98/0.97  --prop_solver_per_cl                    1000
% 2.98/0.97  --min_unsat_core                        false
% 2.98/0.97  --soft_assumptions                      false
% 2.98/0.97  --soft_lemma_size                       3
% 2.98/0.97  --prop_impl_unit_size                   0
% 2.98/0.97  --prop_impl_unit                        []
% 2.98/0.97  --share_sel_clauses                     true
% 2.98/0.97  --reset_solvers                         false
% 2.98/0.97  --bc_imp_inh                            [conj_cone]
% 2.98/0.97  --conj_cone_tolerance                   3.
% 2.98/0.97  --extra_neg_conj                        none
% 2.98/0.97  --large_theory_mode                     true
% 2.98/0.97  --prolific_symb_bound                   200
% 2.98/0.97  --lt_threshold                          2000
% 2.98/0.97  --clause_weak_htbl                      true
% 2.98/0.97  --gc_record_bc_elim                     false
% 2.98/0.97  
% 2.98/0.97  ------ Preprocessing Options
% 2.98/0.97  
% 2.98/0.97  --preprocessing_flag                    true
% 2.98/0.97  --time_out_prep_mult                    0.1
% 2.98/0.97  --splitting_mode                        input
% 2.98/0.97  --splitting_grd                         true
% 2.98/0.97  --splitting_cvd                         false
% 2.98/0.97  --splitting_cvd_svl                     false
% 2.98/0.97  --splitting_nvd                         32
% 2.98/0.97  --sub_typing                            true
% 2.98/0.97  --prep_gs_sim                           true
% 2.98/0.97  --prep_unflatten                        true
% 2.98/0.97  --prep_res_sim                          true
% 2.98/0.97  --prep_upred                            true
% 2.98/0.97  --prep_sem_filter                       exhaustive
% 2.98/0.97  --prep_sem_filter_out                   false
% 2.98/0.97  --pred_elim                             true
% 2.98/0.97  --res_sim_input                         true
% 2.98/0.97  --eq_ax_congr_red                       true
% 2.98/0.97  --pure_diseq_elim                       true
% 2.98/0.97  --brand_transform                       false
% 2.98/0.97  --non_eq_to_eq                          false
% 2.98/0.97  --prep_def_merge                        true
% 2.98/0.97  --prep_def_merge_prop_impl              false
% 2.98/0.97  --prep_def_merge_mbd                    true
% 2.98/0.97  --prep_def_merge_tr_red                 false
% 2.98/0.97  --prep_def_merge_tr_cl                  false
% 2.98/0.97  --smt_preprocessing                     true
% 2.98/0.97  --smt_ac_axioms                         fast
% 2.98/0.97  --preprocessed_out                      false
% 2.98/0.97  --preprocessed_stats                    false
% 2.98/0.97  
% 2.98/0.97  ------ Abstraction refinement Options
% 2.98/0.97  
% 2.98/0.97  --abstr_ref                             []
% 2.98/0.97  --abstr_ref_prep                        false
% 2.98/0.97  --abstr_ref_until_sat                   false
% 2.98/0.97  --abstr_ref_sig_restrict                funpre
% 2.98/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.97  --abstr_ref_under                       []
% 2.98/0.97  
% 2.98/0.97  ------ SAT Options
% 2.98/0.97  
% 2.98/0.97  --sat_mode                              false
% 2.98/0.97  --sat_fm_restart_options                ""
% 2.98/0.97  --sat_gr_def                            false
% 2.98/0.97  --sat_epr_types                         true
% 2.98/0.97  --sat_non_cyclic_types                  false
% 2.98/0.97  --sat_finite_models                     false
% 2.98/0.97  --sat_fm_lemmas                         false
% 2.98/0.97  --sat_fm_prep                           false
% 2.98/0.97  --sat_fm_uc_incr                        true
% 2.98/0.97  --sat_out_model                         small
% 2.98/0.97  --sat_out_clauses                       false
% 2.98/0.97  
% 2.98/0.97  ------ QBF Options
% 2.98/0.97  
% 2.98/0.97  --qbf_mode                              false
% 2.98/0.97  --qbf_elim_univ                         false
% 2.98/0.97  --qbf_dom_inst                          none
% 2.98/0.97  --qbf_dom_pre_inst                      false
% 2.98/0.97  --qbf_sk_in                             false
% 2.98/0.97  --qbf_pred_elim                         true
% 2.98/0.97  --qbf_split                             512
% 2.98/0.97  
% 2.98/0.97  ------ BMC1 Options
% 2.98/0.97  
% 2.98/0.97  --bmc1_incremental                      false
% 2.98/0.97  --bmc1_axioms                           reachable_all
% 2.98/0.97  --bmc1_min_bound                        0
% 2.98/0.97  --bmc1_max_bound                        -1
% 2.98/0.97  --bmc1_max_bound_default                -1
% 2.98/0.97  --bmc1_symbol_reachability              true
% 2.98/0.97  --bmc1_property_lemmas                  false
% 2.98/0.97  --bmc1_k_induction                      false
% 2.98/0.97  --bmc1_non_equiv_states                 false
% 2.98/0.97  --bmc1_deadlock                         false
% 2.98/0.97  --bmc1_ucm                              false
% 2.98/0.97  --bmc1_add_unsat_core                   none
% 2.98/0.97  --bmc1_unsat_core_children              false
% 2.98/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.97  --bmc1_out_stat                         full
% 2.98/0.97  --bmc1_ground_init                      false
% 2.98/0.97  --bmc1_pre_inst_next_state              false
% 2.98/0.97  --bmc1_pre_inst_state                   false
% 2.98/0.97  --bmc1_pre_inst_reach_state             false
% 2.98/0.97  --bmc1_out_unsat_core                   false
% 2.98/0.97  --bmc1_aig_witness_out                  false
% 2.98/0.97  --bmc1_verbose                          false
% 2.98/0.97  --bmc1_dump_clauses_tptp                false
% 2.98/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.97  --bmc1_dump_file                        -
% 2.98/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.97  --bmc1_ucm_extend_mode                  1
% 2.98/0.97  --bmc1_ucm_init_mode                    2
% 2.98/0.97  --bmc1_ucm_cone_mode                    none
% 2.98/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.97  --bmc1_ucm_relax_model                  4
% 2.98/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.97  --bmc1_ucm_layered_model                none
% 2.98/0.97  --bmc1_ucm_max_lemma_size               10
% 2.98/0.97  
% 2.98/0.97  ------ AIG Options
% 2.98/0.97  
% 2.98/0.97  --aig_mode                              false
% 2.98/0.97  
% 2.98/0.97  ------ Instantiation Options
% 2.98/0.97  
% 2.98/0.97  --instantiation_flag                    true
% 2.98/0.97  --inst_sos_flag                         false
% 2.98/0.97  --inst_sos_phase                        true
% 2.98/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.97  --inst_lit_sel_side                     num_symb
% 2.98/0.97  --inst_solver_per_active                1400
% 2.98/0.97  --inst_solver_calls_frac                1.
% 2.98/0.97  --inst_passive_queue_type               priority_queues
% 2.98/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.97  --inst_passive_queues_freq              [25;2]
% 2.98/0.97  --inst_dismatching                      true
% 2.98/0.97  --inst_eager_unprocessed_to_passive     true
% 2.98/0.97  --inst_prop_sim_given                   true
% 2.98/0.97  --inst_prop_sim_new                     false
% 2.98/0.97  --inst_subs_new                         false
% 2.98/0.97  --inst_eq_res_simp                      false
% 2.98/0.97  --inst_subs_given                       false
% 2.98/0.97  --inst_orphan_elimination               true
% 2.98/0.97  --inst_learning_loop_flag               true
% 2.98/0.97  --inst_learning_start                   3000
% 2.98/0.97  --inst_learning_factor                  2
% 2.98/0.97  --inst_start_prop_sim_after_learn       3
% 2.98/0.97  --inst_sel_renew                        solver
% 2.98/0.97  --inst_lit_activity_flag                true
% 2.98/0.97  --inst_restr_to_given                   false
% 2.98/0.97  --inst_activity_threshold               500
% 2.98/0.97  --inst_out_proof                        true
% 2.98/0.97  
% 2.98/0.97  ------ Resolution Options
% 2.98/0.97  
% 2.98/0.97  --resolution_flag                       true
% 2.98/0.97  --res_lit_sel                           adaptive
% 2.98/0.97  --res_lit_sel_side                      none
% 2.98/0.97  --res_ordering                          kbo
% 2.98/0.97  --res_to_prop_solver                    active
% 2.98/0.97  --res_prop_simpl_new                    false
% 2.98/0.97  --res_prop_simpl_given                  true
% 2.98/0.97  --res_passive_queue_type                priority_queues
% 2.98/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.97  --res_passive_queues_freq               [15;5]
% 2.98/0.97  --res_forward_subs                      full
% 2.98/0.97  --res_backward_subs                     full
% 2.98/0.97  --res_forward_subs_resolution           true
% 2.98/0.97  --res_backward_subs_resolution          true
% 2.98/0.97  --res_orphan_elimination                true
% 2.98/0.97  --res_time_limit                        2.
% 2.98/0.97  --res_out_proof                         true
% 2.98/0.97  
% 2.98/0.97  ------ Superposition Options
% 2.98/0.97  
% 2.98/0.97  --superposition_flag                    true
% 2.98/0.97  --sup_passive_queue_type                priority_queues
% 2.98/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.97  --demod_completeness_check              fast
% 2.98/0.97  --demod_use_ground                      true
% 2.98/0.97  --sup_to_prop_solver                    passive
% 2.98/0.97  --sup_prop_simpl_new                    true
% 2.98/0.97  --sup_prop_simpl_given                  true
% 2.98/0.97  --sup_fun_splitting                     false
% 2.98/0.97  --sup_smt_interval                      50000
% 2.98/0.97  
% 2.98/0.97  ------ Superposition Simplification Setup
% 2.98/0.97  
% 2.98/0.97  --sup_indices_passive                   []
% 2.98/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_full_bw                           [BwDemod]
% 2.98/0.97  --sup_immed_triv                        [TrivRules]
% 2.98/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_immed_bw_main                     []
% 2.98/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.97  
% 2.98/0.97  ------ Combination Options
% 2.98/0.97  
% 2.98/0.97  --comb_res_mult                         3
% 2.98/0.97  --comb_sup_mult                         2
% 2.98/0.97  --comb_inst_mult                        10
% 2.98/0.97  
% 2.98/0.97  ------ Debug Options
% 2.98/0.97  
% 2.98/0.97  --dbg_backtrace                         false
% 2.98/0.97  --dbg_dump_prop_clauses                 false
% 2.98/0.97  --dbg_dump_prop_clauses_file            -
% 2.98/0.97  --dbg_out_stat                          false
% 2.98/0.97  ------ Parsing...
% 2.98/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.97  
% 2.98/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.98/0.97  
% 2.98/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.97  
% 2.98/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.97  ------ Proving...
% 2.98/0.97  ------ Problem Properties 
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  clauses                                 26
% 2.98/0.97  conjectures                             5
% 2.98/0.97  EPR                                     8
% 2.98/0.97  Horn                                    20
% 2.98/0.97  unary                                   7
% 2.98/0.97  binary                                  9
% 2.98/0.97  lits                                    65
% 2.98/0.97  lits eq                                 23
% 2.98/0.97  fd_pure                                 0
% 2.98/0.97  fd_pseudo                               0
% 2.98/0.97  fd_cond                                 0
% 2.98/0.97  fd_pseudo_cond                          3
% 2.98/0.97  AC symbols                              0
% 2.98/0.97  
% 2.98/0.97  ------ Schedule dynamic 5 is on 
% 2.98/0.97  
% 2.98/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  ------ 
% 2.98/0.97  Current options:
% 2.98/0.97  ------ 
% 2.98/0.97  
% 2.98/0.97  ------ Input Options
% 2.98/0.97  
% 2.98/0.97  --out_options                           all
% 2.98/0.97  --tptp_safe_out                         true
% 2.98/0.97  --problem_path                          ""
% 2.98/0.97  --include_path                          ""
% 2.98/0.97  --clausifier                            res/vclausify_rel
% 2.98/0.97  --clausifier_options                    --mode clausify
% 2.98/0.97  --stdin                                 false
% 2.98/0.97  --stats_out                             all
% 2.98/0.97  
% 2.98/0.97  ------ General Options
% 2.98/0.97  
% 2.98/0.97  --fof                                   false
% 2.98/0.97  --time_out_real                         305.
% 2.98/0.97  --time_out_virtual                      -1.
% 2.98/0.97  --symbol_type_check                     false
% 2.98/0.97  --clausify_out                          false
% 2.98/0.97  --sig_cnt_out                           false
% 2.98/0.97  --trig_cnt_out                          false
% 2.98/0.97  --trig_cnt_out_tolerance                1.
% 2.98/0.97  --trig_cnt_out_sk_spl                   false
% 2.98/0.97  --abstr_cl_out                          false
% 2.98/0.97  
% 2.98/0.97  ------ Global Options
% 2.98/0.97  
% 2.98/0.97  --schedule                              default
% 2.98/0.97  --add_important_lit                     false
% 2.98/0.97  --prop_solver_per_cl                    1000
% 2.98/0.97  --min_unsat_core                        false
% 2.98/0.97  --soft_assumptions                      false
% 2.98/0.97  --soft_lemma_size                       3
% 2.98/0.97  --prop_impl_unit_size                   0
% 2.98/0.97  --prop_impl_unit                        []
% 2.98/0.97  --share_sel_clauses                     true
% 2.98/0.97  --reset_solvers                         false
% 2.98/0.97  --bc_imp_inh                            [conj_cone]
% 2.98/0.97  --conj_cone_tolerance                   3.
% 2.98/0.97  --extra_neg_conj                        none
% 2.98/0.97  --large_theory_mode                     true
% 2.98/0.97  --prolific_symb_bound                   200
% 2.98/0.97  --lt_threshold                          2000
% 2.98/0.97  --clause_weak_htbl                      true
% 2.98/0.97  --gc_record_bc_elim                     false
% 2.98/0.97  
% 2.98/0.97  ------ Preprocessing Options
% 2.98/0.97  
% 2.98/0.97  --preprocessing_flag                    true
% 2.98/0.97  --time_out_prep_mult                    0.1
% 2.98/0.97  --splitting_mode                        input
% 2.98/0.97  --splitting_grd                         true
% 2.98/0.97  --splitting_cvd                         false
% 2.98/0.97  --splitting_cvd_svl                     false
% 2.98/0.97  --splitting_nvd                         32
% 2.98/0.97  --sub_typing                            true
% 2.98/0.97  --prep_gs_sim                           true
% 2.98/0.97  --prep_unflatten                        true
% 2.98/0.97  --prep_res_sim                          true
% 2.98/0.97  --prep_upred                            true
% 2.98/0.97  --prep_sem_filter                       exhaustive
% 2.98/0.97  --prep_sem_filter_out                   false
% 2.98/0.97  --pred_elim                             true
% 2.98/0.97  --res_sim_input                         true
% 2.98/0.97  --eq_ax_congr_red                       true
% 2.98/0.97  --pure_diseq_elim                       true
% 2.98/0.97  --brand_transform                       false
% 2.98/0.97  --non_eq_to_eq                          false
% 2.98/0.97  --prep_def_merge                        true
% 2.98/0.97  --prep_def_merge_prop_impl              false
% 2.98/0.97  --prep_def_merge_mbd                    true
% 2.98/0.97  --prep_def_merge_tr_red                 false
% 2.98/0.97  --prep_def_merge_tr_cl                  false
% 2.98/0.97  --smt_preprocessing                     true
% 2.98/0.97  --smt_ac_axioms                         fast
% 2.98/0.97  --preprocessed_out                      false
% 2.98/0.97  --preprocessed_stats                    false
% 2.98/0.97  
% 2.98/0.97  ------ Abstraction refinement Options
% 2.98/0.97  
% 2.98/0.97  --abstr_ref                             []
% 2.98/0.97  --abstr_ref_prep                        false
% 2.98/0.97  --abstr_ref_until_sat                   false
% 2.98/0.97  --abstr_ref_sig_restrict                funpre
% 2.98/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.97  --abstr_ref_under                       []
% 2.98/0.97  
% 2.98/0.97  ------ SAT Options
% 2.98/0.97  
% 2.98/0.97  --sat_mode                              false
% 2.98/0.97  --sat_fm_restart_options                ""
% 2.98/0.97  --sat_gr_def                            false
% 2.98/0.97  --sat_epr_types                         true
% 2.98/0.97  --sat_non_cyclic_types                  false
% 2.98/0.97  --sat_finite_models                     false
% 2.98/0.97  --sat_fm_lemmas                         false
% 2.98/0.97  --sat_fm_prep                           false
% 2.98/0.97  --sat_fm_uc_incr                        true
% 2.98/0.97  --sat_out_model                         small
% 2.98/0.97  --sat_out_clauses                       false
% 2.98/0.97  
% 2.98/0.97  ------ QBF Options
% 2.98/0.97  
% 2.98/0.97  --qbf_mode                              false
% 2.98/0.97  --qbf_elim_univ                         false
% 2.98/0.97  --qbf_dom_inst                          none
% 2.98/0.97  --qbf_dom_pre_inst                      false
% 2.98/0.97  --qbf_sk_in                             false
% 2.98/0.97  --qbf_pred_elim                         true
% 2.98/0.97  --qbf_split                             512
% 2.98/0.97  
% 2.98/0.97  ------ BMC1 Options
% 2.98/0.97  
% 2.98/0.97  --bmc1_incremental                      false
% 2.98/0.97  --bmc1_axioms                           reachable_all
% 2.98/0.97  --bmc1_min_bound                        0
% 2.98/0.97  --bmc1_max_bound                        -1
% 2.98/0.97  --bmc1_max_bound_default                -1
% 2.98/0.97  --bmc1_symbol_reachability              true
% 2.98/0.97  --bmc1_property_lemmas                  false
% 2.98/0.97  --bmc1_k_induction                      false
% 2.98/0.97  --bmc1_non_equiv_states                 false
% 2.98/0.97  --bmc1_deadlock                         false
% 2.98/0.97  --bmc1_ucm                              false
% 2.98/0.97  --bmc1_add_unsat_core                   none
% 2.98/0.97  --bmc1_unsat_core_children              false
% 2.98/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.97  --bmc1_out_stat                         full
% 2.98/0.97  --bmc1_ground_init                      false
% 2.98/0.97  --bmc1_pre_inst_next_state              false
% 2.98/0.97  --bmc1_pre_inst_state                   false
% 2.98/0.97  --bmc1_pre_inst_reach_state             false
% 2.98/0.97  --bmc1_out_unsat_core                   false
% 2.98/0.97  --bmc1_aig_witness_out                  false
% 2.98/0.97  --bmc1_verbose                          false
% 2.98/0.97  --bmc1_dump_clauses_tptp                false
% 2.98/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.97  --bmc1_dump_file                        -
% 2.98/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.97  --bmc1_ucm_extend_mode                  1
% 2.98/0.97  --bmc1_ucm_init_mode                    2
% 2.98/0.97  --bmc1_ucm_cone_mode                    none
% 2.98/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.97  --bmc1_ucm_relax_model                  4
% 2.98/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.97  --bmc1_ucm_layered_model                none
% 2.98/0.97  --bmc1_ucm_max_lemma_size               10
% 2.98/0.97  
% 2.98/0.97  ------ AIG Options
% 2.98/0.97  
% 2.98/0.97  --aig_mode                              false
% 2.98/0.97  
% 2.98/0.97  ------ Instantiation Options
% 2.98/0.97  
% 2.98/0.97  --instantiation_flag                    true
% 2.98/0.97  --inst_sos_flag                         false
% 2.98/0.97  --inst_sos_phase                        true
% 2.98/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.97  --inst_lit_sel_side                     none
% 2.98/0.97  --inst_solver_per_active                1400
% 2.98/0.97  --inst_solver_calls_frac                1.
% 2.98/0.97  --inst_passive_queue_type               priority_queues
% 2.98/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.97  --inst_passive_queues_freq              [25;2]
% 2.98/0.97  --inst_dismatching                      true
% 2.98/0.97  --inst_eager_unprocessed_to_passive     true
% 2.98/0.97  --inst_prop_sim_given                   true
% 2.98/0.97  --inst_prop_sim_new                     false
% 2.98/0.97  --inst_subs_new                         false
% 2.98/0.97  --inst_eq_res_simp                      false
% 2.98/0.97  --inst_subs_given                       false
% 2.98/0.97  --inst_orphan_elimination               true
% 2.98/0.97  --inst_learning_loop_flag               true
% 2.98/0.97  --inst_learning_start                   3000
% 2.98/0.97  --inst_learning_factor                  2
% 2.98/0.97  --inst_start_prop_sim_after_learn       3
% 2.98/0.97  --inst_sel_renew                        solver
% 2.98/0.97  --inst_lit_activity_flag                true
% 2.98/0.97  --inst_restr_to_given                   false
% 2.98/0.97  --inst_activity_threshold               500
% 2.98/0.97  --inst_out_proof                        true
% 2.98/0.97  
% 2.98/0.97  ------ Resolution Options
% 2.98/0.97  
% 2.98/0.97  --resolution_flag                       false
% 2.98/0.97  --res_lit_sel                           adaptive
% 2.98/0.97  --res_lit_sel_side                      none
% 2.98/0.97  --res_ordering                          kbo
% 2.98/0.97  --res_to_prop_solver                    active
% 2.98/0.97  --res_prop_simpl_new                    false
% 2.98/0.97  --res_prop_simpl_given                  true
% 2.98/0.97  --res_passive_queue_type                priority_queues
% 2.98/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.97  --res_passive_queues_freq               [15;5]
% 2.98/0.97  --res_forward_subs                      full
% 2.98/0.97  --res_backward_subs                     full
% 2.98/0.97  --res_forward_subs_resolution           true
% 2.98/0.97  --res_backward_subs_resolution          true
% 2.98/0.97  --res_orphan_elimination                true
% 2.98/0.97  --res_time_limit                        2.
% 2.98/0.97  --res_out_proof                         true
% 2.98/0.97  
% 2.98/0.97  ------ Superposition Options
% 2.98/0.97  
% 2.98/0.97  --superposition_flag                    true
% 2.98/0.97  --sup_passive_queue_type                priority_queues
% 2.98/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.97  --demod_completeness_check              fast
% 2.98/0.97  --demod_use_ground                      true
% 2.98/0.97  --sup_to_prop_solver                    passive
% 2.98/0.97  --sup_prop_simpl_new                    true
% 2.98/0.97  --sup_prop_simpl_given                  true
% 2.98/0.97  --sup_fun_splitting                     false
% 2.98/0.97  --sup_smt_interval                      50000
% 2.98/0.97  
% 2.98/0.97  ------ Superposition Simplification Setup
% 2.98/0.97  
% 2.98/0.97  --sup_indices_passive                   []
% 2.98/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_full_bw                           [BwDemod]
% 2.98/0.97  --sup_immed_triv                        [TrivRules]
% 2.98/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_immed_bw_main                     []
% 2.98/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.97  
% 2.98/0.97  ------ Combination Options
% 2.98/0.97  
% 2.98/0.97  --comb_res_mult                         3
% 2.98/0.97  --comb_sup_mult                         2
% 2.98/0.97  --comb_inst_mult                        10
% 2.98/0.97  
% 2.98/0.97  ------ Debug Options
% 2.98/0.97  
% 2.98/0.97  --dbg_backtrace                         false
% 2.98/0.97  --dbg_dump_prop_clauses                 false
% 2.98/0.97  --dbg_dump_prop_clauses_file            -
% 2.98/0.97  --dbg_out_stat                          false
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  ------ Proving...
% 2.98/0.97  
% 2.98/0.97  
% 2.98/0.97  % SZS status Theorem for theBenchmark.p
% 2.98/0.97  
% 2.98/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.97  
% 2.98/0.97  fof(f11,axiom,(
% 2.98/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f23,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(ennf_transformation,[],[f11])).
% 2.98/0.98  
% 2.98/0.98  fof(f24,plain,(
% 2.98/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(flattening,[],[f23])).
% 2.98/0.98  
% 2.98/0.98  fof(f37,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(nnf_transformation,[],[f24])).
% 2.98/0.98  
% 2.98/0.98  fof(f58,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f37])).
% 2.98/0.98  
% 2.98/0.98  fof(f12,conjecture,(
% 2.98/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f13,negated_conjecture,(
% 2.98/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.98/0.98    inference(negated_conjecture,[],[f12])).
% 2.98/0.98  
% 2.98/0.98  fof(f25,plain,(
% 2.98/0.98    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.98/0.98    inference(ennf_transformation,[],[f13])).
% 2.98/0.98  
% 2.98/0.98  fof(f26,plain,(
% 2.98/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.98/0.98    inference(flattening,[],[f25])).
% 2.98/0.98  
% 2.98/0.98  fof(f39,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f38,plain,(
% 2.98/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f40,plain,(
% 2.98/0.98    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38])).
% 2.98/0.98  
% 2.98/0.98  fof(f68,plain,(
% 2.98/0.98    v1_funct_2(sK5,sK2,sK3)),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f69,plain,(
% 2.98/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f9,axiom,(
% 2.98/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f20,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(ennf_transformation,[],[f9])).
% 2.98/0.98  
% 2.98/0.98  fof(f55,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f20])).
% 2.98/0.98  
% 2.98/0.98  fof(f65,plain,(
% 2.98/0.98    v1_funct_2(sK4,sK2,sK3)),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f66,plain,(
% 2.98/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f6,axiom,(
% 2.98/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f16,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.98/0.98    inference(ennf_transformation,[],[f6])).
% 2.98/0.98  
% 2.98/0.98  fof(f17,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(flattening,[],[f16])).
% 2.98/0.98  
% 2.98/0.98  fof(f34,plain,(
% 2.98/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f35,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f34])).
% 2.98/0.98  
% 2.98/0.98  fof(f51,plain,(
% 2.98/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f35])).
% 2.98/0.98  
% 2.98/0.98  fof(f67,plain,(
% 2.98/0.98    v1_funct_1(sK5)),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f7,axiom,(
% 2.98/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f18,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(ennf_transformation,[],[f7])).
% 2.98/0.98  
% 2.98/0.98  fof(f53,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f18])).
% 2.98/0.98  
% 2.98/0.98  fof(f64,plain,(
% 2.98/0.98    v1_funct_1(sK4)),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f10,axiom,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f21,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.98/0.98    inference(ennf_transformation,[],[f10])).
% 2.98/0.98  
% 2.98/0.98  fof(f22,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(flattening,[],[f21])).
% 2.98/0.98  
% 2.98/0.98  fof(f36,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(nnf_transformation,[],[f22])).
% 2.98/0.98  
% 2.98/0.98  fof(f57,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f36])).
% 2.98/0.98  
% 2.98/0.98  fof(f74,plain,(
% 2.98/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(equality_resolution,[],[f57])).
% 2.98/0.98  
% 2.98/0.98  fof(f71,plain,(
% 2.98/0.98    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f3,axiom,(
% 2.98/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f31,plain,(
% 2.98/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/0.98    inference(nnf_transformation,[],[f3])).
% 2.98/0.98  
% 2.98/0.98  fof(f32,plain,(
% 2.98/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/0.98    inference(flattening,[],[f31])).
% 2.98/0.98  
% 2.98/0.98  fof(f47,plain,(
% 2.98/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f32])).
% 2.98/0.98  
% 2.98/0.98  fof(f45,plain,(
% 2.98/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.98/0.98    inference(cnf_transformation,[],[f32])).
% 2.98/0.98  
% 2.98/0.98  fof(f73,plain,(
% 2.98/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.98/0.98    inference(equality_resolution,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f70,plain,(
% 2.98/0.98    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f40])).
% 2.98/0.98  
% 2.98/0.98  fof(f52,plain,(
% 2.98/0.98    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f35])).
% 2.98/0.98  
% 2.98/0.98  fof(f62,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f37])).
% 2.98/0.98  
% 2.98/0.98  fof(f77,plain,(
% 2.98/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.98/0.98    inference(equality_resolution,[],[f62])).
% 2.98/0.98  
% 2.98/0.98  fof(f4,axiom,(
% 2.98/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f33,plain,(
% 2.98/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.98/0.98    inference(nnf_transformation,[],[f4])).
% 2.98/0.98  
% 2.98/0.98  fof(f48,plain,(
% 2.98/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f33])).
% 2.98/0.98  
% 2.98/0.98  fof(f1,axiom,(
% 2.98/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f14,plain,(
% 2.98/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.98/0.98    inference(ennf_transformation,[],[f1])).
% 2.98/0.98  
% 2.98/0.98  fof(f27,plain,(
% 2.98/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.98/0.98    inference(nnf_transformation,[],[f14])).
% 2.98/0.98  
% 2.98/0.98  fof(f28,plain,(
% 2.98/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.98/0.98    inference(rectify,[],[f27])).
% 2.98/0.98  
% 2.98/0.98  fof(f29,plain,(
% 2.98/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f30,plain,(
% 2.98/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.98/0.98  
% 2.98/0.98  fof(f42,plain,(
% 2.98/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f30])).
% 2.98/0.98  
% 2.98/0.98  fof(f5,axiom,(
% 2.98/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f15,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/0.98    inference(ennf_transformation,[],[f5])).
% 2.98/0.98  
% 2.98/0.98  fof(f50,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f15])).
% 2.98/0.98  
% 2.98/0.98  fof(f49,plain,(
% 2.98/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f33])).
% 2.98/0.98  
% 2.98/0.98  fof(f8,axiom,(
% 2.98/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f19,plain,(
% 2.98/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f8])).
% 2.98/0.98  
% 2.98/0.98  fof(f54,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f19])).
% 2.98/0.98  
% 2.98/0.98  fof(f2,axiom,(
% 2.98/0.98    v1_xboole_0(k1_xboole_0)),
% 2.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f44,plain,(
% 2.98/0.98    v1_xboole_0(k1_xboole_0)),
% 2.98/0.98    inference(cnf_transformation,[],[f2])).
% 2.98/0.98  
% 2.98/0.98  cnf(c_22,plain,
% 2.98/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.98/0.98      | k1_xboole_0 = X2 ),
% 2.98/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_26,negated_conjecture,
% 2.98/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.98/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_485,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.98/0.98      | sK5 != X0
% 2.98/0.98      | sK3 != X2
% 2.98/0.98      | sK2 != X1
% 2.98/0.98      | k1_xboole_0 = X2 ),
% 2.98/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_486,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.98/0.98      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.98/0.98      | k1_xboole_0 = sK3 ),
% 2.98/0.98      inference(unflattening,[status(thm)],[c_485]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_25,negated_conjecture,
% 2.98/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.98/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_488,plain,
% 2.98/0.98      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_486,c_25]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2115,plain,
% 2.98/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_14,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2117,plain,
% 2.98/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.98/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2955,plain,
% 2.98/0.98      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2115,c_2117]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3054,plain,
% 2.98/0.98      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_488,c_2955]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_29,negated_conjecture,
% 2.98/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.98/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_496,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.98/0.98      | sK4 != X0
% 2.98/0.98      | sK3 != X2
% 2.98/0.98      | sK2 != X1
% 2.98/0.98      | k1_xboole_0 = X2 ),
% 2.98/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_497,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.98/0.98      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.98/0.98      | k1_xboole_0 = sK3 ),
% 2.98/0.98      inference(unflattening,[status(thm)],[c_496]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_28,negated_conjecture,
% 2.98/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.98/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_499,plain,
% 2.98/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_497,c_28]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2113,plain,
% 2.98/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2956,plain,
% 2.98/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2113,c_2117]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3057,plain,
% 2.98/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_499,c_2956]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_11,plain,
% 2.98/0.98      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.98/0.98      | ~ v1_relat_1(X1)
% 2.98/0.98      | ~ v1_relat_1(X0)
% 2.98/0.98      | ~ v1_funct_1(X1)
% 2.98/0.98      | ~ v1_funct_1(X0)
% 2.98/0.98      | X1 = X0
% 2.98/0.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2120,plain,
% 2.98/0.98      ( X0 = X1
% 2.98/0.98      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.98/0.98      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.98/0.98      | v1_relat_1(X1) != iProver_top
% 2.98/0.98      | v1_relat_1(X0) != iProver_top
% 2.98/0.98      | v1_funct_1(X0) != iProver_top
% 2.98/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3371,plain,
% 2.98/0.98      ( k1_relat_1(X0) != sK2
% 2.98/0.98      | sK5 = X0
% 2.98/0.98      | sK3 = k1_xboole_0
% 2.98/0.98      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.98/0.98      | v1_relat_1(X0) != iProver_top
% 2.98/0.98      | v1_relat_1(sK5) != iProver_top
% 2.98/0.98      | v1_funct_1(X0) != iProver_top
% 2.98/0.98      | v1_funct_1(sK5) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3054,c_2120]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_27,negated_conjecture,
% 2.98/0.98      ( v1_funct_1(sK5) ),
% 2.98/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_34,plain,
% 2.98/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_36,plain,
% 2.98/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_12,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | v1_relat_1(X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2318,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.98/0.98      | v1_relat_1(sK5) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2319,plain,
% 2.98/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.98/0.98      | v1_relat_1(sK5) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3722,plain,
% 2.98/0.98      ( v1_funct_1(X0) != iProver_top
% 2.98/0.98      | k1_relat_1(X0) != sK2
% 2.98/0.98      | sK5 = X0
% 2.98/0.98      | sK3 = k1_xboole_0
% 2.98/0.98      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.98/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3371,c_34,c_36,c_2319]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3723,plain,
% 2.98/0.98      ( k1_relat_1(X0) != sK2
% 2.98/0.98      | sK5 = X0
% 2.98/0.98      | sK3 = k1_xboole_0
% 2.98/0.98      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.98/0.98      | v1_relat_1(X0) != iProver_top
% 2.98/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_3722]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3735,plain,
% 2.98/0.98      ( sK5 = sK4
% 2.98/0.98      | sK3 = k1_xboole_0
% 2.98/0.98      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.98/0.98      | v1_relat_1(sK4) != iProver_top
% 2.98/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3057,c_3723]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_30,negated_conjecture,
% 2.98/0.98      ( v1_funct_1(sK4) ),
% 2.98/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_31,plain,
% 2.98/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_33,plain,
% 2.98/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_15,plain,
% 2.98/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 2.98/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.98/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_23,negated_conjecture,
% 2.98/0.98      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.98/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_402,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | sK5 != X0
% 2.98/0.98      | sK4 != X0
% 2.98/0.98      | sK3 != X2
% 2.98/0.98      | sK2 != X1 ),
% 2.98/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_403,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.98/0.98      | sK4 != sK5 ),
% 2.98/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2321,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.98/0.98      | v1_relat_1(sK4) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2322,plain,
% 2.98/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.98/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4,plain,
% 2.98/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.98/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2416,plain,
% 2.98/0.98      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2621,plain,
% 2.98/0.98      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_6,plain,
% 2.98/0.98      ( r1_tarski(X0,X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2622,plain,
% 2.98/0.98      ( r1_tarski(sK4,sK4) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1553,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2347,plain,
% 2.98/0.98      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_1553]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2985,plain,
% 2.98/0.98      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2347]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3748,plain,
% 2.98/0.98      ( sK3 = k1_xboole_0
% 2.98/0.98      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3735,c_31,c_33,c_25,c_403,c_2322,c_2621,c_2622,c_2985]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3754,plain,
% 2.98/0.98      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3057,c_3748]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_24,negated_conjecture,
% 2.98/0.98      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2116,plain,
% 2.98/0.98      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.98/0.98      | r2_hidden(X0,sK2) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3861,plain,
% 2.98/0.98      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.98/0.98      | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3754,c_2116]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_10,plain,
% 2.98/0.98      ( ~ v1_relat_1(X0)
% 2.98/0.98      | ~ v1_relat_1(X1)
% 2.98/0.98      | ~ v1_funct_1(X0)
% 2.98/0.98      | ~ v1_funct_1(X1)
% 2.98/0.98      | X0 = X1
% 2.98/0.98      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.98/0.98      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2121,plain,
% 2.98/0.98      ( X0 = X1
% 2.98/0.98      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.98/0.98      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.98/0.98      | v1_relat_1(X0) != iProver_top
% 2.98/0.98      | v1_relat_1(X1) != iProver_top
% 2.98/0.98      | v1_funct_1(X1) != iProver_top
% 2.98/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3886,plain,
% 2.98/0.98      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.98/0.98      | sK5 = sK4
% 2.98/0.98      | sK3 = k1_xboole_0
% 2.98/0.98      | v1_relat_1(sK5) != iProver_top
% 2.98/0.98      | v1_relat_1(sK4) != iProver_top
% 2.98/0.98      | v1_funct_1(sK5) != iProver_top
% 2.98/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3861,c_2121]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3887,plain,
% 2.98/0.98      ( ~ v1_relat_1(sK5)
% 2.98/0.98      | ~ v1_relat_1(sK4)
% 2.98/0.98      | ~ v1_funct_1(sK5)
% 2.98/0.98      | ~ v1_funct_1(sK4)
% 2.98/0.98      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.98/0.98      | sK5 = sK4
% 2.98/0.98      | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3886]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3945,plain,
% 2.98/0.98      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3886,c_30,c_28,c_27,c_25,c_403,c_2318,c_2321,c_2621,
% 2.98/0.98                 c_2622,c_2985,c_3887]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3949,plain,
% 2.98/0.98      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_3054,c_3945]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3950,plain,
% 2.98/0.98      ( sK3 = k1_xboole_0 ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3949,c_3057]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_18,plain,
% 2.98/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.98/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.98/0.98      | k1_xboole_0 = X1
% 2.98/0.98      | k1_xboole_0 = X0 ),
% 2.98/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_439,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.98/0.98      | sK4 != X0
% 2.98/0.98      | sK3 != k1_xboole_0
% 2.98/0.98      | sK2 != X1
% 2.98/0.98      | k1_xboole_0 = X0
% 2.98/0.98      | k1_xboole_0 = X1 ),
% 2.98/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_440,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.98/0.98      | sK3 != k1_xboole_0
% 2.98/0.98      | k1_xboole_0 = sK4
% 2.98/0.98      | k1_xboole_0 = sK2 ),
% 2.98/0.98      inference(unflattening,[status(thm)],[c_439]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2109,plain,
% 2.98/0.98      ( sK3 != k1_xboole_0
% 2.98/0.98      | k1_xboole_0 = sK4
% 2.98/0.98      | k1_xboole_0 = sK2
% 2.98/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3962,plain,
% 2.98/0.98      ( sK4 = k1_xboole_0
% 2.98/0.98      | sK2 = k1_xboole_0
% 2.98/0.98      | k1_xboole_0 != k1_xboole_0
% 2.98/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2109]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3991,plain,
% 2.98/0.98      ( sK4 = k1_xboole_0
% 2.98/0.98      | sK2 = k1_xboole_0
% 2.98/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(equality_resolution_simp,[status(thm)],[c_3962]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3970,plain,
% 2.98/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2113]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3995,plain,
% 2.98/0.98      ( sK4 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.98/0.98      inference(forward_subsumption_resolution,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3991,c_3970]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2426,plain,
% 2.98/0.98      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_1553]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2984,plain,
% 2.98/0.98      ( sK5 != X0 | sK5 = sK4 | sK4 != X0 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2426]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2986,plain,
% 2.98/0.98      ( sK5 = sK4 | sK5 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2984]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_423,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.98/0.98      | sK5 != X0
% 2.98/0.98      | sK3 != k1_xboole_0
% 2.98/0.98      | sK2 != X1
% 2.98/0.98      | k1_xboole_0 = X0
% 2.98/0.98      | k1_xboole_0 = X1 ),
% 2.98/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_424,plain,
% 2.98/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.98/0.98      | sK3 != k1_xboole_0
% 2.98/0.98      | k1_xboole_0 = sK5
% 2.98/0.98      | k1_xboole_0 = sK2 ),
% 2.98/0.98      inference(unflattening,[status(thm)],[c_423]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2110,plain,
% 2.98/0.98      ( sK3 != k1_xboole_0
% 2.98/0.98      | k1_xboole_0 = sK5
% 2.98/0.98      | k1_xboole_0 = sK2
% 2.98/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3961,plain,
% 2.98/0.98      ( sK5 = k1_xboole_0
% 2.98/0.98      | sK2 = k1_xboole_0
% 2.98/0.98      | k1_xboole_0 != k1_xboole_0
% 2.98/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2110]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3998,plain,
% 2.98/0.98      ( sK5 = k1_xboole_0
% 2.98/0.98      | sK2 = k1_xboole_0
% 2.98/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.98/0.98      inference(equality_resolution_simp,[status(thm)],[c_3961]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3969,plain,
% 2.98/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2115]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4002,plain,
% 2.98/0.98      ( sK5 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.98/0.98      inference(forward_subsumption_resolution,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3998,c_3969]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4736,plain,
% 2.98/0.98      ( sK2 = k1_xboole_0 ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3995,c_25,c_403,c_2621,c_2622,c_2986,c_2985,c_4002]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_8,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2122,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2638,plain,
% 2.98/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2113,c_2122]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3964,plain,
% 2.98/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2638]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4740,plain,
% 2.98/0.98      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_4736,c_3964]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2128,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.98/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_9,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.98      | ~ r2_hidden(X2,X0)
% 2.98/0.98      | ~ v1_xboole_0(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_7,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_231,plain,
% 2.98/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.98/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_232,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_231]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_294,plain,
% 2.98/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.98/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_232]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2111,plain,
% 2.98/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.98/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.98/0.98      | v1_xboole_0(X2) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2900,plain,
% 2.98/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.98/0.98      | r1_tarski(X0,X2) = iProver_top
% 2.98/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2128,c_2111]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5705,plain,
% 2.98/0.98      ( r1_tarski(sK4,X0) = iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_4740,c_2900]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5724,plain,
% 2.98/0.98      ( r1_tarski(sK4,k1_xboole_0) = iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_5705]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2637,plain,
% 2.98/0.98      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2115,c_2122]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3965,plain,
% 2.98/0.98      ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_3950,c_2637]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4739,plain,
% 2.98/0.98      ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_4736,c_3965]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5680,plain,
% 2.98/0.98      ( r1_tarski(sK5,X0) = iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_4739,c_2900]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5699,plain,
% 2.98/0.98      ( r1_tarski(sK5,k1_xboole_0) = iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_5680]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2124,plain,
% 2.98/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2123,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.98/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_13,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | ~ v1_xboole_0(X2)
% 2.98/0.98      | v1_xboole_0(X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2118,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.98/0.98      | v1_xboole_0(X2) != iProver_top
% 2.98/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3266,plain,
% 2.98/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.98/0.98      | v1_xboole_0(X2) != iProver_top
% 2.98/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2123,c_2118]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5290,plain,
% 2.98/0.98      ( v1_xboole_0(X0) != iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2124,c_3266]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5297,plain,
% 2.98/0.98      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 2.98/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_5290]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4058,plain,
% 2.98/0.98      ( ~ r2_hidden(sK0(X0,sK4),X0)
% 2.98/0.98      | ~ r1_tarski(X0,X1)
% 2.98/0.98      | ~ v1_xboole_0(X1) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_294]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4059,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK4),X0) != iProver_top
% 2.98/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.98/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_4058]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4061,plain,
% 2.98/0.98      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.98/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_4059]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3147,plain,
% 2.98/0.98      ( ~ r2_hidden(sK0(X0,sK5),X0)
% 2.98/0.98      | ~ r1_tarski(X0,X1)
% 2.98/0.98      | ~ v1_xboole_0(X1) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_294]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3148,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK5),X0) != iProver_top
% 2.98/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.98/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_3147]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3150,plain,
% 2.98/0.98      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.98/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_3148]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2651,plain,
% 2.98/0.98      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2652,plain,
% 2.98/0.98      ( sK4 = X0
% 2.98/0.98      | r1_tarski(X0,sK4) != iProver_top
% 2.98/0.98      | r1_tarski(sK4,X0) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2654,plain,
% 2.98/0.98      ( sK4 = k1_xboole_0
% 2.98/0.98      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2652]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2606,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK4),X0) | r1_tarski(X0,sK4) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2617,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK4),X0) = iProver_top
% 2.98/0.98      | r1_tarski(X0,sK4) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2619,plain,
% 2.98/0.98      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2617]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2585,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2596,plain,
% 2.98/0.98      ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
% 2.98/0.98      | r1_tarski(X0,sK5) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2598,plain,
% 2.98/0.98      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2596]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2500,plain,
% 2.98/0.98      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2501,plain,
% 2.98/0.98      ( sK5 = X0
% 2.98/0.98      | r1_tarski(X0,sK5) != iProver_top
% 2.98/0.98      | r1_tarski(sK5,X0) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_2500]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2503,plain,
% 2.98/0.98      ( sK5 = k1_xboole_0
% 2.98/0.98      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.98/0.98      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2501]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2348,plain,
% 2.98/0.98      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_2347]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3,plain,
% 2.98/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_94,plain,
% 2.98/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_87,plain,
% 2.98/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_89,plain,
% 2.98/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.98/0.98      inference(instantiation,[status(thm)],[c_87]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(contradiction,plain,
% 2.98/0.98      ( $false ),
% 2.98/0.98      inference(minisat,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_5724,c_5699,c_5297,c_4061,c_3150,c_2654,c_2619,c_2598,
% 2.98/0.98                 c_2503,c_2348,c_403,c_94,c_89,c_25]) ).
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  ------                               Statistics
% 2.98/0.98  
% 2.98/0.98  ------ General
% 2.98/0.98  
% 2.98/0.98  abstr_ref_over_cycles:                  0
% 2.98/0.98  abstr_ref_under_cycles:                 0
% 2.98/0.98  gc_basic_clause_elim:                   0
% 2.98/0.98  forced_gc_time:                         0
% 2.98/0.98  parsing_time:                           0.01
% 2.98/0.98  unif_index_cands_time:                  0.
% 2.98/0.98  unif_index_add_time:                    0.
% 2.98/0.98  orderings_time:                         0.
% 2.98/0.98  out_proof_time:                         0.013
% 2.98/0.98  total_time:                             0.168
% 2.98/0.98  num_of_symbols:                         51
% 2.98/0.98  num_of_terms:                           3971
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing
% 2.98/0.98  
% 2.98/0.98  num_of_splits:                          0
% 2.98/0.98  num_of_split_atoms:                     0
% 2.98/0.98  num_of_reused_defs:                     0
% 2.98/0.98  num_eq_ax_congr_red:                    26
% 2.98/0.98  num_of_sem_filtered_clauses:            1
% 2.98/0.98  num_of_subtypes:                        0
% 2.98/0.98  monotx_restored_types:                  0
% 2.98/0.98  sat_num_of_epr_types:                   0
% 2.98/0.98  sat_num_of_non_cyclic_types:            0
% 2.98/0.98  sat_guarded_non_collapsed_types:        0
% 2.98/0.98  num_pure_diseq_elim:                    0
% 2.98/0.98  simp_replaced_by:                       0
% 2.98/0.98  res_preprocessed:                       129
% 2.98/0.98  prep_upred:                             0
% 2.98/0.98  prep_unflattend:                        71
% 2.98/0.98  smt_new_axioms:                         0
% 2.98/0.98  pred_elim_cands:                        6
% 2.98/0.98  pred_elim:                              2
% 2.98/0.98  pred_elim_cl:                           4
% 2.98/0.98  pred_elim_cycles:                       4
% 2.98/0.98  merged_defs:                            8
% 2.98/0.98  merged_defs_ncl:                        0
% 2.98/0.98  bin_hyper_res:                          9
% 2.98/0.98  prep_cycles:                            4
% 2.98/0.98  pred_elim_time:                         0.016
% 2.98/0.98  splitting_time:                         0.
% 2.98/0.98  sem_filter_time:                        0.
% 2.98/0.98  monotx_time:                            0.001
% 2.98/0.98  subtype_inf_time:                       0.
% 2.98/0.98  
% 2.98/0.98  ------ Problem properties
% 2.98/0.98  
% 2.98/0.98  clauses:                                26
% 2.98/0.98  conjectures:                            5
% 2.98/0.98  epr:                                    8
% 2.98/0.98  horn:                                   20
% 2.98/0.98  ground:                                 12
% 2.98/0.98  unary:                                  7
% 2.98/0.98  binary:                                 9
% 2.98/0.98  lits:                                   65
% 2.98/0.98  lits_eq:                                23
% 2.98/0.98  fd_pure:                                0
% 2.98/0.98  fd_pseudo:                              0
% 2.98/0.98  fd_cond:                                0
% 2.98/0.98  fd_pseudo_cond:                         3
% 2.98/0.98  ac_symbols:                             0
% 2.98/0.98  
% 2.98/0.98  ------ Propositional Solver
% 2.98/0.98  
% 2.98/0.98  prop_solver_calls:                      28
% 2.98/0.98  prop_fast_solver_calls:                 1076
% 2.98/0.98  smt_solver_calls:                       0
% 2.98/0.98  smt_fast_solver_calls:                  0
% 2.98/0.98  prop_num_of_clauses:                    1715
% 2.98/0.98  prop_preprocess_simplified:             5206
% 2.98/0.98  prop_fo_subsumed:                       41
% 2.98/0.98  prop_solver_time:                       0.
% 2.98/0.98  smt_solver_time:                        0.
% 2.98/0.98  smt_fast_solver_time:                   0.
% 2.98/0.98  prop_fast_solver_time:                  0.
% 2.98/0.98  prop_unsat_core_time:                   0.
% 2.98/0.98  
% 2.98/0.98  ------ QBF
% 2.98/0.98  
% 2.98/0.98  qbf_q_res:                              0
% 2.98/0.98  qbf_num_tautologies:                    0
% 2.98/0.98  qbf_prep_cycles:                        0
% 2.98/0.98  
% 2.98/0.98  ------ BMC1
% 2.98/0.98  
% 2.98/0.98  bmc1_current_bound:                     -1
% 2.98/0.98  bmc1_last_solved_bound:                 -1
% 2.98/0.98  bmc1_unsat_core_size:                   -1
% 2.98/0.98  bmc1_unsat_core_parents_size:           -1
% 2.98/0.98  bmc1_merge_next_fun:                    0
% 2.98/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation
% 2.98/0.98  
% 2.98/0.98  inst_num_of_clauses:                    489
% 2.98/0.98  inst_num_in_passive:                    32
% 2.98/0.98  inst_num_in_active:                     286
% 2.98/0.98  inst_num_in_unprocessed:                173
% 2.98/0.98  inst_num_of_loops:                      380
% 2.98/0.98  inst_num_of_learning_restarts:          0
% 2.98/0.98  inst_num_moves_active_passive:          91
% 2.98/0.98  inst_lit_activity:                      0
% 2.98/0.98  inst_lit_activity_moves:                0
% 2.98/0.98  inst_num_tautologies:                   0
% 2.98/0.98  inst_num_prop_implied:                  0
% 2.98/0.98  inst_num_existing_simplified:           0
% 2.98/0.98  inst_num_eq_res_simplified:             0
% 2.98/0.98  inst_num_child_elim:                    0
% 2.98/0.98  inst_num_of_dismatching_blockings:      127
% 2.98/0.98  inst_num_of_non_proper_insts:           460
% 2.98/0.98  inst_num_of_duplicates:                 0
% 2.98/0.98  inst_inst_num_from_inst_to_res:         0
% 2.98/0.98  inst_dismatching_checking_time:         0.
% 2.98/0.98  
% 2.98/0.98  ------ Resolution
% 2.98/0.98  
% 2.98/0.98  res_num_of_clauses:                     0
% 2.98/0.98  res_num_in_passive:                     0
% 2.98/0.98  res_num_in_active:                      0
% 2.98/0.98  res_num_of_loops:                       133
% 2.98/0.98  res_forward_subset_subsumed:            50
% 2.98/0.98  res_backward_subset_subsumed:           4
% 2.98/0.98  res_forward_subsumed:                   0
% 2.98/0.98  res_backward_subsumed:                  0
% 2.98/0.98  res_forward_subsumption_resolution:     0
% 2.98/0.98  res_backward_subsumption_resolution:    0
% 2.98/0.98  res_clause_to_clause_subsumption:       289
% 2.98/0.98  res_orphan_elimination:                 0
% 2.98/0.98  res_tautology_del:                      63
% 2.98/0.98  res_num_eq_res_simplified:              0
% 2.98/0.98  res_num_sel_changes:                    0
% 2.98/0.98  res_moves_from_active_to_pass:          0
% 2.98/0.98  
% 2.98/0.98  ------ Superposition
% 2.98/0.98  
% 2.98/0.98  sup_time_total:                         0.
% 2.98/0.98  sup_time_generating:                    0.
% 2.98/0.98  sup_time_sim_full:                      0.
% 2.98/0.98  sup_time_sim_immed:                     0.
% 2.98/0.98  
% 2.98/0.98  sup_num_of_clauses:                     67
% 2.98/0.98  sup_num_in_active:                      41
% 2.98/0.98  sup_num_in_passive:                     26
% 2.98/0.98  sup_num_of_loops:                       75
% 2.98/0.98  sup_fw_superposition:                   46
% 2.98/0.98  sup_bw_superposition:                   55
% 2.98/0.98  sup_immediate_simplified:               6
% 2.98/0.98  sup_given_eliminated:                   0
% 2.98/0.98  comparisons_done:                       0
% 2.98/0.98  comparisons_avoided:                    11
% 2.98/0.98  
% 2.98/0.98  ------ Simplifications
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  sim_fw_subset_subsumed:                 3
% 2.98/0.98  sim_bw_subset_subsumed:                 10
% 2.98/0.98  sim_fw_subsumed:                        1
% 2.98/0.98  sim_bw_subsumed:                        0
% 2.98/0.98  sim_fw_subsumption_res:                 2
% 2.98/0.98  sim_bw_subsumption_res:                 0
% 2.98/0.98  sim_tautology_del:                      2
% 2.98/0.98  sim_eq_tautology_del:                   9
% 2.98/0.98  sim_eq_res_simp:                        2
% 2.98/0.98  sim_fw_demodulated:                     0
% 2.98/0.98  sim_bw_demodulated:                     29
% 2.98/0.98  sim_light_normalised:                   3
% 2.98/0.98  sim_joinable_taut:                      0
% 2.98/0.98  sim_joinable_simp:                      0
% 2.98/0.98  sim_ac_normalised:                      0
% 2.98/0.98  sim_smt_subsumption:                    0
% 2.98/0.98  
%------------------------------------------------------------------------------
