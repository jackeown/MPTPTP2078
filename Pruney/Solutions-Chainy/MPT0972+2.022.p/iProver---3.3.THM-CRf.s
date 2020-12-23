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
% DateTime   : Thu Dec  3 12:01:12 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  163 (1555 expanded)
%              Number of clauses        :   97 ( 468 expanded)
%              Number of leaves         :   17 ( 373 expanded)
%              Depth                    :   25
%              Number of atoms          :  542 (9782 expanded)
%              Number of equality atoms :  262 (2367 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(f39,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f41,f40])).

fof(f72,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f75,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f74,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f16])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_493,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_27])).

cnf(c_1960,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1962,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2745,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1960,c_1962])).

cnf(c_2950,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_493,c_2745])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_502,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_504,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_30])).

cnf(c_1958,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2746,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1958,c_1962])).

cnf(c_3026,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_504,c_2746])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1964,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3168,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2950,c_1964])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2158,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2159,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_3646,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3168,c_36,c_38,c_2159])).

cnf(c_3647,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3646])).

cnf(c_3659,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_3647])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_408,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_2161,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2162,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2260,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2498,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2499,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1439,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2187,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_3674,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_3787,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3659,c_33,c_35,c_27,c_408,c_2162,c_2498,c_2499,c_3674])).

cnf(c_3793,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_3787])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1961,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3798,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3793,c_1961])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1965,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3960,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3798,c_1965])).

cnf(c_3976,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3960])).

cnf(c_4401,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_32,c_30,c_29,c_27,c_408,c_2158,c_2161,c_2498,c_2499,c_3674,c_3976])).

cnf(c_4405,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2950,c_4401])).

cnf(c_4775,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4405,c_3026])).

cnf(c_4795,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4775,c_1960])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4801,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4795,c_8])).

cnf(c_4796,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4775,c_1958])).

cnf(c_4798,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4796,c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_395,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_4620,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_4623,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_4599,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_4602,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4599])).

cnf(c_2274,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_3671,plain,
    ( sK5 != X0
    | sK5 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_3675,plain,
    ( sK5 = sK4
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2804,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2805,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_2807,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_2774,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2775,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2774])).

cnf(c_2777,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_2515,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2516,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2515])).

cnf(c_2518,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2483,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK0(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2494,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK0(X0,sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_2496,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_2462,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK0(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2473,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK0(X0,sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2462])).

cnf(c_2475,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2473])).

cnf(c_2405,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2406,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_2408,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4801,c_4798,c_4623,c_4602,c_3674,c_3675,c_2807,c_2777,c_2518,c_2499,c_2498,c_2496,c_2475,c_2408,c_408,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:03:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.94/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/0.99  
% 2.94/0.99  ------  iProver source info
% 2.94/0.99  
% 2.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/0.99  git: non_committed_changes: false
% 2.94/0.99  git: last_make_outside_of_git: false
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     num_symb
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       true
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  ------ Parsing...
% 2.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/0.99  ------ Proving...
% 2.94/0.99  ------ Problem Properties 
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  clauses                                 27
% 2.94/0.99  conjectures                             5
% 2.94/0.99  EPR                                     7
% 2.94/0.99  Horn                                    20
% 2.94/0.99  unary                                   9
% 2.94/0.99  binary                                  9
% 2.94/0.99  lits                                    64
% 2.94/0.99  lits eq                                 28
% 2.94/0.99  fd_pure                                 0
% 2.94/0.99  fd_pseudo                               0
% 2.94/0.99  fd_cond                                 1
% 2.94/0.99  fd_pseudo_cond                          3
% 2.94/0.99  AC symbols                              0
% 2.94/0.99  
% 2.94/0.99  ------ Schedule dynamic 5 is on 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  Current options:
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     none
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       false
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ Proving...
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS status Theorem for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  fof(f11,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f23,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f11])).
% 2.94/0.99  
% 2.94/0.99  fof(f24,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(flattening,[],[f23])).
% 2.94/0.99  
% 2.94/0.99  fof(f39,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f24])).
% 2.94/0.99  
% 2.94/0.99  fof(f62,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f39])).
% 2.94/0.99  
% 2.94/0.99  fof(f12,conjecture,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f13,negated_conjecture,(
% 2.94/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.94/0.99    inference(negated_conjecture,[],[f12])).
% 2.94/0.99  
% 2.94/0.99  fof(f25,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f13])).
% 2.94/0.99  
% 2.94/0.99  fof(f26,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f25])).
% 2.94/0.99  
% 2.94/0.99  fof(f41,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f40,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f42,plain,(
% 2.94/0.99    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f41,f40])).
% 2.94/0.99  
% 2.94/0.99  fof(f72,plain,(
% 2.94/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f73,plain,(
% 2.94/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f9,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f20,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f9])).
% 2.94/0.99  
% 2.94/0.99  fof(f59,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f20])).
% 2.94/0.99  
% 2.94/0.99  fof(f69,plain,(
% 2.94/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f70,plain,(
% 2.94/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f7,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f17,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f7])).
% 2.94/0.99  
% 2.94/0.99  fof(f18,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f17])).
% 2.94/0.99  
% 2.94/0.99  fof(f36,plain,(
% 2.94/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f37,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f36])).
% 2.94/0.99  
% 2.94/0.99  fof(f56,plain,(
% 2.94/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f37])).
% 2.94/0.99  
% 2.94/0.99  fof(f71,plain,(
% 2.94/0.99    v1_funct_1(sK5)),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f8,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f19,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f8])).
% 2.94/0.99  
% 2.94/0.99  fof(f58,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f19])).
% 2.94/0.99  
% 2.94/0.99  fof(f68,plain,(
% 2.94/0.99    v1_funct_1(sK4)),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f10,axiom,(
% 2.94/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f21,plain,(
% 2.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.94/0.99    inference(ennf_transformation,[],[f10])).
% 2.94/0.99  
% 2.94/0.99  fof(f22,plain,(
% 2.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(flattening,[],[f21])).
% 2.94/0.99  
% 2.94/0.99  fof(f38,plain,(
% 2.94/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f22])).
% 2.94/0.99  
% 2.94/0.99  fof(f61,plain,(
% 2.94/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f80,plain,(
% 2.94/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(equality_resolution,[],[f61])).
% 2.94/0.99  
% 2.94/0.99  fof(f75,plain,(
% 2.94/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f4,axiom,(
% 2.94/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f31,plain,(
% 2.94/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.94/0.99    inference(nnf_transformation,[],[f4])).
% 2.94/0.99  
% 2.94/0.99  fof(f32,plain,(
% 2.94/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.94/0.99    inference(flattening,[],[f31])).
% 2.94/0.99  
% 2.94/0.99  fof(f50,plain,(
% 2.94/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f32])).
% 2.94/0.99  
% 2.94/0.99  fof(f48,plain,(
% 2.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.94/0.99    inference(cnf_transformation,[],[f32])).
% 2.94/0.99  
% 2.94/0.99  fof(f77,plain,(
% 2.94/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.94/0.99    inference(equality_resolution,[],[f48])).
% 2.94/0.99  
% 2.94/0.99  fof(f74,plain,(
% 2.94/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f42])).
% 2.94/0.99  
% 2.94/0.99  fof(f57,plain,(
% 2.94/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f37])).
% 2.94/0.99  
% 2.94/0.99  fof(f5,axiom,(
% 2.94/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f33,plain,(
% 2.94/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.99    inference(nnf_transformation,[],[f5])).
% 2.94/0.99  
% 2.94/0.99  fof(f34,plain,(
% 2.94/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.99    inference(flattening,[],[f33])).
% 2.94/0.99  
% 2.94/0.99  fof(f53,plain,(
% 2.94/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.94/0.99    inference(cnf_transformation,[],[f34])).
% 2.94/0.99  
% 2.94/0.99  fof(f78,plain,(
% 2.94/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.94/0.99    inference(equality_resolution,[],[f53])).
% 2.94/0.99  
% 2.94/0.99  fof(f1,axiom,(
% 2.94/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f14,plain,(
% 2.94/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.94/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.94/0.99  
% 2.94/0.99  fof(f15,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f14])).
% 2.94/0.99  
% 2.94/0.99  fof(f43,plain,(
% 2.94/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f15])).
% 2.94/0.99  
% 2.94/0.99  fof(f3,axiom,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f47,plain,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    inference(cnf_transformation,[],[f3])).
% 2.94/0.99  
% 2.94/0.99  fof(f6,axiom,(
% 2.94/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f35,plain,(
% 2.94/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f6])).
% 2.94/0.99  
% 2.94/0.99  fof(f54,plain,(
% 2.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f35])).
% 2.94/0.99  
% 2.94/0.99  fof(f2,axiom,(
% 2.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f16,plain,(
% 2.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f2])).
% 2.94/0.99  
% 2.94/0.99  fof(f27,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(nnf_transformation,[],[f16])).
% 2.94/0.99  
% 2.94/0.99  fof(f28,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(rectify,[],[f27])).
% 2.94/0.99  
% 2.94/0.99  fof(f29,plain,(
% 2.94/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f30,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.94/0.99  
% 2.94/0.99  fof(f45,plain,(
% 2.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f30])).
% 2.94/0.99  
% 2.94/0.99  cnf(c_24,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_28,negated_conjecture,
% 2.94/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.94/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_490,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | sK5 != X0
% 2.94/0.99      | sK3 != X2
% 2.94/0.99      | sK2 != X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_491,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.94/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.94/0.99      | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_27,negated_conjecture,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_493,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_491,c_27]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1960,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_16,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1962,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2745,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1960,c_1962]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2950,plain,
% 2.94/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_493,c_2745]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_31,negated_conjecture,
% 2.94/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_501,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | sK4 != X0
% 2.94/0.99      | sK3 != X2
% 2.94/0.99      | sK2 != X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_502,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.94/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.94/0.99      | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_501]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_30,negated_conjecture,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_504,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_502,c_30]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1958,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2746,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1958,c_1962]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3026,plain,
% 2.94/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_504,c_2746]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_14,plain,
% 2.94/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.94/0.99      | ~ v1_relat_1(X1)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X1)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | X0 = X1
% 2.94/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1964,plain,
% 2.94/0.99      ( X0 = X1
% 2.94/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.94/0.99      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top
% 2.94/0.99      | v1_relat_1(X1) != iProver_top
% 2.94/0.99      | v1_funct_1(X1) != iProver_top
% 2.94/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3168,plain,
% 2.94/0.99      ( k1_relat_1(X0) != sK2
% 2.94/0.99      | sK5 = X0
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top
% 2.94/0.99      | v1_relat_1(sK5) != iProver_top
% 2.94/0.99      | v1_funct_1(X0) != iProver_top
% 2.94/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2950,c_1964]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_29,negated_conjecture,
% 2.94/0.99      ( v1_funct_1(sK5) ),
% 2.94/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_36,plain,
% 2.94/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_38,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_15,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | v1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2158,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.94/0.99      | v1_relat_1(sK5) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2159,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.94/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3646,plain,
% 2.94/0.99      ( v1_funct_1(X0) != iProver_top
% 2.94/0.99      | k1_relat_1(X0) != sK2
% 2.94/0.99      | sK5 = X0
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3168,c_36,c_38,c_2159]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3647,plain,
% 2.94/0.99      ( k1_relat_1(X0) != sK2
% 2.94/0.99      | sK5 = X0
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top
% 2.94/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3646]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3659,plain,
% 2.94/0.99      ( sK5 = sK4
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.94/0.99      | v1_relat_1(sK4) != iProver_top
% 2.94/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3026,c_3647]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_32,negated_conjecture,
% 2.94/0.99      ( v1_funct_1(sK4) ),
% 2.94/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_33,plain,
% 2.94/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_35,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_17,plain,
% 2.94/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_25,negated_conjecture,
% 2.94/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.94/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_407,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | sK5 != X0
% 2.94/0.99      | sK4 != X0
% 2.94/0.99      | sK3 != X2
% 2.94/0.99      | sK2 != X1 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_408,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.94/0.99      | sK4 != sK5 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2161,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.94/0.99      | v1_relat_1(sK4) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2162,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.94/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.94/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2260,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2498,plain,
% 2.94/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2260]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_7,plain,
% 2.94/0.99      ( r1_tarski(X0,X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2499,plain,
% 2.94/0.99      ( r1_tarski(sK4,sK4) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1439,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2187,plain,
% 2.94/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3674,plain,
% 2.94/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2187]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3787,plain,
% 2.94/0.99      ( sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3659,c_33,c_35,c_27,c_408,c_2162,c_2498,c_2499,c_3674]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3793,plain,
% 2.94/0.99      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3026,c_3787]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_26,negated_conjecture,
% 2.94/0.99      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1961,plain,
% 2.94/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.94/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3798,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.94/0.99      | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3793,c_1961]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_13,plain,
% 2.94/0.99      ( ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X1)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X1)
% 2.94/0.99      | X1 = X0
% 2.94/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.94/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1965,plain,
% 2.94/0.99      ( X0 = X1
% 2.94/0.99      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.94/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.94/0.99      | v1_relat_1(X1) != iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top
% 2.94/0.99      | v1_funct_1(X0) != iProver_top
% 2.94/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3960,plain,
% 2.94/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.94/0.99      | sK5 = sK4
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | v1_relat_1(sK5) != iProver_top
% 2.94/0.99      | v1_relat_1(sK4) != iProver_top
% 2.94/0.99      | v1_funct_1(sK5) != iProver_top
% 2.94/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3798,c_1965]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3976,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK5)
% 2.94/0.99      | ~ v1_relat_1(sK4)
% 2.94/0.99      | ~ v1_funct_1(sK5)
% 2.94/0.99      | ~ v1_funct_1(sK4)
% 2.94/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.94/0.99      | sK5 = sK4
% 2.94/0.99      | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3960]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4401,plain,
% 2.94/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3960,c_32,c_30,c_29,c_27,c_408,c_2158,c_2161,c_2498,
% 2.94/0.99                 c_2499,c_3674,c_3976]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4405,plain,
% 2.94/0.99      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2950,c_4401]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4775,plain,
% 2.94/0.99      ( sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_4405,c_3026]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4795,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4775,c_1960]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_8,plain,
% 2.94/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4801,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4795,c_8]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4796,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4775,c_1958]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4798,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4796,c_8]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_0,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4,plain,
% 2.94/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_394,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_395,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_394]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4620,plain,
% 2.94/0.99      ( ~ r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_395]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4623,plain,
% 2.94/0.99      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4599,plain,
% 2.94/0.99      ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_395]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4602,plain,
% 2.94/0.99      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4599]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2274,plain,
% 2.94/0.99      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3671,plain,
% 2.94/0.99      ( sK5 != X0 | sK5 = sK4 | sK4 != X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2274]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3675,plain,
% 2.94/0.99      ( sK5 = sK4 | sK5 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_3671]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_12,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2804,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2805,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.94/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2804]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2807,plain,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.94/0.99      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2805]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2774,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2775,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 2.94/0.99      | r1_tarski(sK5,X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2774]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2777,plain,
% 2.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.94/0.99      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2515,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2516,plain,
% 2.94/0.99      ( sK4 = X0
% 2.94/0.99      | r1_tarski(X0,sK4) != iProver_top
% 2.94/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2515]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2518,plain,
% 2.94/0.99      ( sK4 = k1_xboole_0
% 2.94/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.94/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2516]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2,plain,
% 2.94/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2483,plain,
% 2.94/0.99      ( r1_tarski(X0,sK4) | r2_hidden(sK0(X0,sK4),X0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2494,plain,
% 2.94/0.99      ( r1_tarski(X0,sK4) = iProver_top
% 2.94/0.99      | r2_hidden(sK0(X0,sK4),X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2496,plain,
% 2.94/0.99      ( r1_tarski(k1_xboole_0,sK4) = iProver_top
% 2.94/0.99      | r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2494]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2462,plain,
% 2.94/0.99      ( r1_tarski(X0,sK5) | r2_hidden(sK0(X0,sK5),X0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2473,plain,
% 2.94/0.99      ( r1_tarski(X0,sK5) = iProver_top
% 2.94/0.99      | r2_hidden(sK0(X0,sK5),X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2462]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2475,plain,
% 2.94/0.99      ( r1_tarski(k1_xboole_0,sK5) = iProver_top
% 2.94/0.99      | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2473]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2405,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2406,plain,
% 2.94/0.99      ( sK5 = X0
% 2.94/0.99      | r1_tarski(X0,sK5) != iProver_top
% 2.94/0.99      | r1_tarski(sK5,X0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2408,plain,
% 2.94/0.99      ( sK5 = k1_xboole_0
% 2.94/0.99      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.94/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_2406]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(contradiction,plain,
% 2.94/0.99      ( $false ),
% 2.94/0.99      inference(minisat,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_4801,c_4798,c_4623,c_4602,c_3674,c_3675,c_2807,c_2777,
% 2.94/0.99                 c_2518,c_2499,c_2498,c_2496,c_2475,c_2408,c_408,c_27]) ).
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  ------                               Statistics
% 2.94/0.99  
% 2.94/0.99  ------ General
% 2.94/0.99  
% 2.94/0.99  abstr_ref_over_cycles:                  0
% 2.94/0.99  abstr_ref_under_cycles:                 0
% 2.94/0.99  gc_basic_clause_elim:                   0
% 2.94/0.99  forced_gc_time:                         0
% 2.94/0.99  parsing_time:                           0.008
% 2.94/0.99  unif_index_cands_time:                  0.
% 2.94/0.99  unif_index_add_time:                    0.
% 2.94/0.99  orderings_time:                         0.
% 2.94/0.99  out_proof_time:                         0.008
% 2.94/0.99  total_time:                             0.145
% 2.94/0.99  num_of_symbols:                         51
% 2.94/0.99  num_of_terms:                           3670
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing
% 2.94/0.99  
% 2.94/0.99  num_of_splits:                          0
% 2.94/0.99  num_of_split_atoms:                     0
% 2.94/0.99  num_of_reused_defs:                     0
% 2.94/0.99  num_eq_ax_congr_red:                    26
% 2.94/0.99  num_of_sem_filtered_clauses:            1
% 2.94/0.99  num_of_subtypes:                        0
% 2.94/0.99  monotx_restored_types:                  0
% 2.94/0.99  sat_num_of_epr_types:                   0
% 2.94/0.99  sat_num_of_non_cyclic_types:            0
% 2.94/0.99  sat_guarded_non_collapsed_types:        0
% 2.94/0.99  num_pure_diseq_elim:                    0
% 2.94/0.99  simp_replaced_by:                       0
% 2.94/0.99  res_preprocessed:                       132
% 2.94/0.99  prep_upred:                             0
% 2.94/0.99  prep_unflattend:                        66
% 2.94/0.99  smt_new_axioms:                         0
% 2.94/0.99  pred_elim_cands:                        5
% 2.94/0.99  pred_elim:                              3
% 2.94/0.99  pred_elim_cl:                           5
% 2.94/0.99  pred_elim_cycles:                       5
% 2.94/0.99  merged_defs:                            8
% 2.94/0.99  merged_defs_ncl:                        0
% 2.94/0.99  bin_hyper_res:                          8
% 2.94/0.99  prep_cycles:                            4
% 2.94/0.99  pred_elim_time:                         0.015
% 2.94/0.99  splitting_time:                         0.
% 2.94/0.99  sem_filter_time:                        0.
% 2.94/0.99  monotx_time:                            0.
% 2.94/0.99  subtype_inf_time:                       0.
% 2.94/0.99  
% 2.94/0.99  ------ Problem properties
% 2.94/0.99  
% 2.94/0.99  clauses:                                27
% 2.94/0.99  conjectures:                            5
% 2.94/0.99  epr:                                    7
% 2.94/0.99  horn:                                   20
% 2.94/0.99  ground:                                 11
% 2.94/0.99  unary:                                  9
% 2.94/0.99  binary:                                 9
% 2.94/0.99  lits:                                   64
% 2.94/0.99  lits_eq:                                28
% 2.94/0.99  fd_pure:                                0
% 2.94/0.99  fd_pseudo:                              0
% 2.94/0.99  fd_cond:                                1
% 2.94/0.99  fd_pseudo_cond:                         3
% 2.94/0.99  ac_symbols:                             0
% 2.94/0.99  
% 2.94/0.99  ------ Propositional Solver
% 2.94/0.99  
% 2.94/0.99  prop_solver_calls:                      28
% 2.94/0.99  prop_fast_solver_calls:                 993
% 2.94/0.99  smt_solver_calls:                       0
% 2.94/0.99  smt_fast_solver_calls:                  0
% 2.94/0.99  prop_num_of_clauses:                    1376
% 2.94/0.99  prop_preprocess_simplified:             4715
% 2.94/0.99  prop_fo_subsumed:                       19
% 2.94/0.99  prop_solver_time:                       0.
% 2.94/0.99  smt_solver_time:                        0.
% 2.94/0.99  smt_fast_solver_time:                   0.
% 2.94/0.99  prop_fast_solver_time:                  0.
% 2.94/0.99  prop_unsat_core_time:                   0.
% 2.94/0.99  
% 2.94/0.99  ------ QBF
% 2.94/0.99  
% 2.94/0.99  qbf_q_res:                              0
% 2.94/0.99  qbf_num_tautologies:                    0
% 2.94/0.99  qbf_prep_cycles:                        0
% 2.94/0.99  
% 2.94/0.99  ------ BMC1
% 2.94/0.99  
% 2.94/0.99  bmc1_current_bound:                     -1
% 2.94/0.99  bmc1_last_solved_bound:                 -1
% 2.94/0.99  bmc1_unsat_core_size:                   -1
% 2.94/0.99  bmc1_unsat_core_parents_size:           -1
% 2.94/0.99  bmc1_merge_next_fun:                    0
% 2.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation
% 2.94/0.99  
% 2.94/0.99  inst_num_of_clauses:                    413
% 2.94/0.99  inst_num_in_passive:                    66
% 2.94/0.99  inst_num_in_active:                     240
% 2.94/0.99  inst_num_in_unprocessed:                107
% 2.94/0.99  inst_num_of_loops:                      320
% 2.94/0.99  inst_num_of_learning_restarts:          0
% 2.94/0.99  inst_num_moves_active_passive:          77
% 2.94/0.99  inst_lit_activity:                      0
% 2.94/0.99  inst_lit_activity_moves:                0
% 2.94/0.99  inst_num_tautologies:                   0
% 2.94/0.99  inst_num_prop_implied:                  0
% 2.94/0.99  inst_num_existing_simplified:           0
% 2.94/0.99  inst_num_eq_res_simplified:             0
% 2.94/0.99  inst_num_child_elim:                    0
% 2.94/0.99  inst_num_of_dismatching_blockings:      145
% 2.94/0.99  inst_num_of_non_proper_insts:           451
% 2.94/0.99  inst_num_of_duplicates:                 0
% 2.94/0.99  inst_inst_num_from_inst_to_res:         0
% 2.94/0.99  inst_dismatching_checking_time:         0.
% 2.94/0.99  
% 2.94/0.99  ------ Resolution
% 2.94/0.99  
% 2.94/0.99  res_num_of_clauses:                     0
% 2.94/0.99  res_num_in_passive:                     0
% 2.94/0.99  res_num_in_active:                      0
% 2.94/0.99  res_num_of_loops:                       136
% 2.94/0.99  res_forward_subset_subsumed:            38
% 2.94/0.99  res_backward_subset_subsumed:           0
% 2.94/0.99  res_forward_subsumed:                   0
% 2.94/0.99  res_backward_subsumed:                  0
% 2.94/0.99  res_forward_subsumption_resolution:     0
% 2.94/0.99  res_backward_subsumption_resolution:    0
% 2.94/0.99  res_clause_to_clause_subsumption:       254
% 2.94/0.99  res_orphan_elimination:                 0
% 2.94/0.99  res_tautology_del:                      53
% 2.94/0.99  res_num_eq_res_simplified:              0
% 2.94/0.99  res_num_sel_changes:                    0
% 2.94/0.99  res_moves_from_active_to_pass:          0
% 2.94/0.99  
% 2.94/0.99  ------ Superposition
% 2.94/0.99  
% 2.94/0.99  sup_time_total:                         0.
% 2.94/0.99  sup_time_generating:                    0.
% 2.94/0.99  sup_time_sim_full:                      0.
% 2.94/0.99  sup_time_sim_immed:                     0.
% 2.94/0.99  
% 2.94/0.99  sup_num_of_clauses:                     62
% 2.94/0.99  sup_num_in_active:                      40
% 2.94/0.99  sup_num_in_passive:                     22
% 2.94/0.99  sup_num_of_loops:                       63
% 2.94/0.99  sup_fw_superposition:                   69
% 2.94/0.99  sup_bw_superposition:                   11
% 2.94/0.99  sup_immediate_simplified:               13
% 2.94/0.99  sup_given_eliminated:                   0
% 2.94/0.99  comparisons_done:                       0
% 2.94/0.99  comparisons_avoided:                    14
% 2.94/0.99  
% 2.94/0.99  ------ Simplifications
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  sim_fw_subset_subsumed:                 1
% 2.94/0.99  sim_bw_subset_subsumed:                 4
% 2.94/0.99  sim_fw_subsumed:                        0
% 2.94/0.99  sim_bw_subsumed:                        0
% 2.94/0.99  sim_fw_subsumption_res:                 4
% 2.94/0.99  sim_bw_subsumption_res:                 0
% 2.94/0.99  sim_tautology_del:                      2
% 2.94/0.99  sim_eq_tautology_del:                   14
% 2.94/0.99  sim_eq_res_simp:                        2
% 2.94/0.99  sim_fw_demodulated:                     12
% 2.94/0.99  sim_bw_demodulated:                     19
% 2.94/0.99  sim_light_normalised:                   2
% 2.94/0.99  sim_joinable_taut:                      0
% 2.94/0.99  sim_joinable_simp:                      0
% 2.94/0.99  sim_ac_normalised:                      0
% 2.94/0.99  sim_smt_subsumption:                    0
% 2.94/0.99  
%------------------------------------------------------------------------------
