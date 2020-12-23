%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:16 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  160 (1214 expanded)
%              Number of clauses        :  100 ( 394 expanded)
%              Number of leaves         :   18 ( 293 expanded)
%              Depth                    :   26
%              Number of atoms          :  531 (7581 expanded)
%              Number of equality atoms :  269 (1794 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK8)
        & ! [X4] :
            ( k1_funct_1(sK8,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK8,X0,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
          ( ~ r2_relset_1(sK5,sK6,sK7,X3)
          & ! [X4] :
              ( k1_funct_1(sK7,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
    & ! [X4] :
        ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
        | ~ r2_hidden(X4,sK5) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f38,f56,f55])).

fof(f93,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
      | ~ r2_hidden(X4,sK5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1579,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK8 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_682,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_684,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_33])).

cnf(c_1566,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1568,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2217,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1566,c_1568])).

cnf(c_2340,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_684,c_2217])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_693,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_695,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_36])).

cnf(c_1564,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2218,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1564,c_1568])).

cnf(c_2368,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_695,c_2218])).

cnf(c_20,plain,
    ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1570,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2583,plain,
    ( k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_1570])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2173,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2174,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2519,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3005,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_3006,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3005])).

cnf(c_3138,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2583,c_39,c_41,c_2174,c_3006])).

cnf(c_3139,plain,
    ( k1_relat_1(X0) != sK5
    | sK7 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3138])).

cnf(c_3144,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_3139])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1944,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_2141,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2142,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2141])).

cnf(c_3148,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3144,c_42,c_44,c_2142,c_2174])).

cnf(c_3152,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK7,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_3148])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1567,plain,
    ( k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3518,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK8)) = k1_funct_1(sK8,sK4(sK7,sK8))
    | sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3152,c_1567])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1571,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3632,plain,
    ( k1_relat_1(sK7) != k1_relat_1(sK8)
    | sK8 = sK7
    | sK6 = k1_xboole_0
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_1571])).

cnf(c_3633,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | k1_relat_1(sK7) != k1_relat_1(sK8)
    | sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3632])).

cnf(c_5355,plain,
    ( k1_relat_1(sK7) != k1_relat_1(sK8)
    | sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3632,c_39,c_41,c_42,c_44,c_2142,c_2174,c_3006])).

cnf(c_5357,plain,
    ( k1_relat_1(sK7) != sK5
    | sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2340,c_5355])).

cnf(c_5460,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5357,c_2368])).

cnf(c_24,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK8 != X3
    | sK7 != X3
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_33])).

cnf(c_1562,plain,
    ( sK7 != sK8
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_5470,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5460,c_1562])).

cnf(c_5481,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1579,c_5470])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1584,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1580,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3902,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_1580])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1585,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4121,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK5,sK6)),sK7) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3902,c_1585])).

cnf(c_4687,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_4121])).

cnf(c_5573,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5481,c_4687])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5623,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5573,c_5])).

cnf(c_3901,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_1580])).

cnf(c_4031,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK5,sK6)),sK8) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_1585])).

cnf(c_4684,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_4031])).

cnf(c_5574,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5481,c_4684])).

cnf(c_5622,plain,
    ( r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5574,c_5])).

cnf(c_5312,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2881,plain,
    ( ~ r1_tarski(sK7,k1_xboole_0)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2882,plain,
    ( k1_xboole_0 = sK7
    | r1_tarski(sK7,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2881])).

cnf(c_2873,plain,
    ( ~ r1_tarski(sK8,k1_xboole_0)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2874,plain,
    ( k1_xboole_0 = sK8
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2873])).

cnf(c_1069,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2202,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2601,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_2602,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2601])).

cnf(c_1068,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2579,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_2133,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1781,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1960,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_1961,plain,
    ( sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_1671,plain,
    ( sK8 != X0
    | sK7 != X0
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1672,plain,
    ( sK8 != k1_xboole_0
    | sK7 = sK8
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5623,c_5622,c_5312,c_2882,c_2874,c_2602,c_2579,c_2133,c_1961,c_1672,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.35/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.98  
% 3.35/0.98  ------  iProver source info
% 3.35/0.98  
% 3.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.98  git: non_committed_changes: false
% 3.35/0.98  git: last_make_outside_of_git: false
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    ""
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.98  --bmc1_non_equiv_states                 false
% 3.35/0.98  --bmc1_deadlock                         false
% 3.35/0.98  --bmc1_ucm                              false
% 3.35/0.98  --bmc1_add_unsat_core                   none
% 3.35/0.98  --bmc1_unsat_core_children              false
% 3.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.98  --bmc1_out_stat                         full
% 3.35/0.98  --bmc1_ground_init                      false
% 3.35/0.98  --bmc1_pre_inst_next_state              false
% 3.35/0.98  --bmc1_pre_inst_state                   false
% 3.35/0.98  --bmc1_pre_inst_reach_state             false
% 3.35/0.98  --bmc1_out_unsat_core                   false
% 3.35/0.98  --bmc1_aig_witness_out                  false
% 3.35/0.98  --bmc1_verbose                          false
% 3.35/0.98  --bmc1_dump_clauses_tptp                false
% 3.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.98  --bmc1_dump_file                        -
% 3.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.98  --bmc1_ucm_extend_mode                  1
% 3.35/0.98  --bmc1_ucm_init_mode                    2
% 3.35/0.98  --bmc1_ucm_cone_mode                    none
% 3.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.98  --bmc1_ucm_relax_model                  4
% 3.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.98  --bmc1_ucm_layered_model                none
% 3.35/0.98  --bmc1_ucm_max_lemma_size               10
% 3.35/0.98  
% 3.35/0.98  ------ AIG Options
% 3.35/0.98  
% 3.35/0.98  --aig_mode                              false
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation Options
% 3.35/0.98  
% 3.35/0.98  --instantiation_flag                    true
% 3.35/0.98  --inst_sos_flag                         true
% 3.35/0.98  --inst_sos_phase                        true
% 3.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel_side                     num_symb
% 3.35/0.98  --inst_solver_per_active                1400
% 3.35/0.98  --inst_solver_calls_frac                1.
% 3.35/0.98  --inst_passive_queue_type               priority_queues
% 3.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.98  --inst_passive_queues_freq              [25;2]
% 3.35/0.98  --inst_dismatching                      true
% 3.35/0.98  --inst_eager_unprocessed_to_passive     true
% 3.35/0.98  --inst_prop_sim_given                   true
% 3.35/0.98  --inst_prop_sim_new                     false
% 3.35/0.98  --inst_subs_new                         false
% 3.35/0.98  --inst_eq_res_simp                      false
% 3.35/0.98  --inst_subs_given                       false
% 3.35/0.98  --inst_orphan_elimination               true
% 3.35/0.98  --inst_learning_loop_flag               true
% 3.35/0.98  --inst_learning_start                   3000
% 3.35/0.98  --inst_learning_factor                  2
% 3.35/0.98  --inst_start_prop_sim_after_learn       3
% 3.35/0.98  --inst_sel_renew                        solver
% 3.35/0.98  --inst_lit_activity_flag                true
% 3.35/0.98  --inst_restr_to_given                   false
% 3.35/0.98  --inst_activity_threshold               500
% 3.35/0.98  --inst_out_proof                        true
% 3.35/0.98  
% 3.35/0.98  ------ Resolution Options
% 3.35/0.98  
% 3.35/0.98  --resolution_flag                       true
% 3.35/0.98  --res_lit_sel                           adaptive
% 3.35/0.98  --res_lit_sel_side                      none
% 3.35/0.98  --res_ordering                          kbo
% 3.35/0.98  --res_to_prop_solver                    active
% 3.35/0.98  --res_prop_simpl_new                    false
% 3.35/0.98  --res_prop_simpl_given                  true
% 3.35/0.98  --res_passive_queue_type                priority_queues
% 3.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.98  --res_passive_queues_freq               [15;5]
% 3.35/0.98  --res_forward_subs                      full
% 3.35/0.98  --res_backward_subs                     full
% 3.35/0.98  --res_forward_subs_resolution           true
% 3.35/0.98  --res_backward_subs_resolution          true
% 3.35/0.98  --res_orphan_elimination                true
% 3.35/0.98  --res_time_limit                        2.
% 3.35/0.98  --res_out_proof                         true
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Options
% 3.35/0.98  
% 3.35/0.98  --superposition_flag                    true
% 3.35/0.98  --sup_passive_queue_type                priority_queues
% 3.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.98  --demod_completeness_check              fast
% 3.35/0.98  --demod_use_ground                      true
% 3.35/0.98  --sup_to_prop_solver                    passive
% 3.35/0.98  --sup_prop_simpl_new                    true
% 3.35/0.98  --sup_prop_simpl_given                  true
% 3.35/0.98  --sup_fun_splitting                     true
% 3.35/0.98  --sup_smt_interval                      50000
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Simplification Setup
% 3.35/0.98  
% 3.35/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.35/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.35/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.35/0.98  --sup_immed_triv                        [TrivRules]
% 3.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_immed_bw_main                     []
% 3.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_input_bw                          []
% 3.35/0.98  
% 3.35/0.98  ------ Combination Options
% 3.35/0.98  
% 3.35/0.98  --comb_res_mult                         3
% 3.35/0.98  --comb_sup_mult                         2
% 3.35/0.98  --comb_inst_mult                        10
% 3.35/0.98  
% 3.35/0.98  ------ Debug Options
% 3.35/0.98  
% 3.35/0.98  --dbg_backtrace                         false
% 3.35/0.98  --dbg_dump_prop_clauses                 false
% 3.35/0.98  --dbg_dump_prop_clauses_file            -
% 3.35/0.98  --dbg_out_stat                          false
% 3.35/0.98  ------ Parsing...
% 3.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.98  ------ Proving...
% 3.35/0.98  ------ Problem Properties 
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  clauses                                 34
% 3.35/0.98  conjectures                             5
% 3.35/0.98  EPR                                     6
% 3.35/0.98  Horn                                    26
% 3.35/0.98  unary                                   9
% 3.35/0.98  binary                                  11
% 3.35/0.98  lits                                    83
% 3.35/0.98  lits eq                                 30
% 3.35/0.98  fd_pure                                 0
% 3.35/0.98  fd_pseudo                               0
% 3.35/0.98  fd_cond                                 2
% 3.35/0.98  fd_pseudo_cond                          4
% 3.35/0.98  AC symbols                              0
% 3.35/0.98  
% 3.35/0.98  ------ Schedule dynamic 5 is on 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  Current options:
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    ""
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         true
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     none
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       false
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     true
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.35/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_input_bw                          []
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ Proving...
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS status Theorem for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  fof(f6,axiom,(
% 3.35/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f67,plain,(
% 3.35/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f6])).
% 3.35/0.99  
% 3.35/0.99  fof(f17,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f35,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f17])).
% 3.35/0.99  
% 3.35/0.99  fof(f36,plain,(
% 3.35/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(flattening,[],[f35])).
% 3.35/0.99  
% 3.35/0.99  fof(f54,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(nnf_transformation,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f83,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f54])).
% 3.35/0.99  
% 3.35/0.99  fof(f18,conjecture,(
% 3.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f19,negated_conjecture,(
% 3.35/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.35/0.99    inference(negated_conjecture,[],[f18])).
% 3.35/0.99  
% 3.35/0.99  fof(f37,plain,(
% 3.35/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.35/0.99    inference(ennf_transformation,[],[f19])).
% 3.35/0.99  
% 3.35/0.99  fof(f38,plain,(
% 3.35/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.35/0.99    inference(flattening,[],[f37])).
% 3.35/0.99  
% 3.35/0.99  fof(f56,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK8) & ! [X4] : (k1_funct_1(sK8,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK8,X0,X1) & v1_funct_1(sK8))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f55,plain,(
% 3.35/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f57,plain,(
% 3.35/0.99    (~r2_relset_1(sK5,sK6,sK7,sK8) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f38,f56,f55])).
% 3.35/0.99  
% 3.35/0.99  fof(f93,plain,(
% 3.35/0.99    v1_funct_2(sK8,sK5,sK6)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f94,plain,(
% 3.35/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f15,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f32,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f15])).
% 3.35/0.99  
% 3.35/0.99  fof(f81,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f90,plain,(
% 3.35/0.99    v1_funct_2(sK7,sK5,sK6)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f91,plain,(
% 3.35/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f12,axiom,(
% 3.35/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f28,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f12])).
% 3.35/0.99  
% 3.35/0.99  fof(f29,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(flattening,[],[f28])).
% 3.35/0.99  
% 3.35/0.99  fof(f52,plain,(
% 3.35/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f53,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f52])).
% 3.35/0.99  
% 3.35/0.99  fof(f77,plain,(
% 3.35/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f53])).
% 3.35/0.99  
% 3.35/0.99  fof(f89,plain,(
% 3.35/0.99    v1_funct_1(sK7)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f11,axiom,(
% 3.35/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f76,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f11])).
% 3.35/0.99  
% 3.35/0.99  fof(f8,axiom,(
% 3.35/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f26,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f8])).
% 3.35/0.99  
% 3.35/0.99  fof(f69,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f26])).
% 3.35/0.99  
% 3.35/0.99  fof(f92,plain,(
% 3.35/0.99    v1_funct_1(sK8)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f95,plain,(
% 3.35/0.99    ( ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f78,plain,(
% 3.35/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f53])).
% 3.35/0.99  
% 3.35/0.99  fof(f16,axiom,(
% 3.35/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f33,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.35/0.99    inference(ennf_transformation,[],[f16])).
% 3.35/0.99  
% 3.35/0.99  fof(f34,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(flattening,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f82,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f96,plain,(
% 3.35/0.99    ~r2_relset_1(sK5,sK6,sK7,sK8)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f1,axiom,(
% 3.35/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f21,plain,(
% 3.35/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f1])).
% 3.35/0.99  
% 3.35/0.99  fof(f39,plain,(
% 3.35/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.35/0.99    inference(nnf_transformation,[],[f21])).
% 3.35/0.99  
% 3.35/0.99  fof(f40,plain,(
% 3.35/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.35/0.99    inference(rectify,[],[f39])).
% 3.35/0.99  
% 3.35/0.99  fof(f41,plain,(
% 3.35/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f42,plain,(
% 3.35/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.35/0.99  
% 3.35/0.99  fof(f59,plain,(
% 3.35/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f42])).
% 3.35/0.99  
% 3.35/0.99  fof(f5,axiom,(
% 3.35/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f23,plain,(
% 3.35/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f5])).
% 3.35/0.99  
% 3.35/0.99  fof(f66,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f23])).
% 3.35/0.99  
% 3.35/0.99  fof(f60,plain,(
% 3.35/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f42])).
% 3.35/0.99  
% 3.35/0.99  fof(f4,axiom,(
% 3.35/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f43,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(nnf_transformation,[],[f4])).
% 3.35/0.99  
% 3.35/0.99  fof(f44,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(flattening,[],[f43])).
% 3.35/0.99  
% 3.35/0.99  fof(f65,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.35/0.99    inference(cnf_transformation,[],[f44])).
% 3.35/0.99  
% 3.35/0.99  fof(f97,plain,(
% 3.35/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f65])).
% 3.35/0.99  
% 3.35/0.99  fof(f3,axiom,(
% 3.35/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f22,plain,(
% 3.35/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.35/0.99    inference(ennf_transformation,[],[f3])).
% 3.35/0.99  
% 3.35/0.99  fof(f62,plain,(
% 3.35/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f22])).
% 3.35/0.99  
% 3.35/0.99  cnf(c_9,plain,
% 3.35/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1579,plain,
% 3.35/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_30,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.35/0.99      | k1_xboole_0 = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_34,negated_conjecture,
% 3.35/0.99      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.35/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_681,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.35/0.99      | sK8 != X0
% 3.35/0.99      | sK6 != X2
% 3.35/0.99      | sK5 != X1
% 3.35/0.99      | k1_xboole_0 = X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_682,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | k1_relset_1(sK5,sK6,sK8) = sK5
% 3.35/0.99      | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_681]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_33,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.35/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_684,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5 | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_682,c_33]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1566,plain,
% 3.35/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_23,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1568,plain,
% 3.35/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2217,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1566,c_1568]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2340,plain,
% 3.35/0.99      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_684,c_2217]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_37,negated_conjecture,
% 3.35/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.35/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_692,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.35/0.99      | sK7 != X0
% 3.35/0.99      | sK6 != X2
% 3.35/0.99      | sK5 != X1
% 3.35/0.99      | k1_xboole_0 = X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_693,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | k1_relset_1(sK5,sK6,sK7) = sK5
% 3.35/0.99      | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_36,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.35/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_695,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_693,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1564,plain,
% 3.35/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2218,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1564,c_1568]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2368,plain,
% 3.35/0.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_695,c_2218]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_20,plain,
% 3.35/0.99      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
% 3.35/0.99      | ~ v1_funct_1(X1)
% 3.35/0.99      | ~ v1_funct_1(X0)
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | ~ v1_relat_1(X1)
% 3.35/0.99      | X1 = X0
% 3.35/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1570,plain,
% 3.35/0.99      ( X0 = X1
% 3.35/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.35/0.99      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_funct_1(X1) != iProver_top
% 3.35/0.99      | v1_relat_1(X1) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2583,plain,
% 3.35/0.99      ( k1_relat_1(X0) != sK5
% 3.35/0.99      | sK7 = X0
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_funct_1(sK7) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2368,c_1570]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_38,negated_conjecture,
% 3.35/0.99      ( v1_funct_1(sK7) ),
% 3.35/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_39,plain,
% 3.35/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_41,plain,
% 3.35/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_18,plain,
% 3.35/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2173,plain,
% 3.35/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2174,plain,
% 3.35/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_11,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.35/0.99      | ~ v1_relat_1(X1)
% 3.35/0.99      | v1_relat_1(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2519,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | v1_relat_1(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3005,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | v1_relat_1(sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2519]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3006,plain,
% 3.35/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.35/0.99      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.35/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3005]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3138,plain,
% 3.35/0.99      ( v1_relat_1(X0) != iProver_top
% 3.35/0.99      | k1_relat_1(X0) != sK5
% 3.35/0.99      | sK7 = X0
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_2583,c_39,c_41,c_2174,c_3006]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3139,plain,
% 3.35/0.99      ( k1_relat_1(X0) != sK5
% 3.35/0.99      | sK7 = X0
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_3138]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3144,plain,
% 3.35/0.99      ( sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7)) = iProver_top
% 3.35/0.99      | v1_funct_1(sK8) != iProver_top
% 3.35/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2340,c_3139]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_35,negated_conjecture,
% 3.35/0.99      ( v1_funct_1(sK8) ),
% 3.35/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_42,plain,
% 3.35/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_44,plain,
% 3.35/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1746,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | v1_relat_1(sK8) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1944,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.35/0.99      | v1_relat_1(sK8) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1746]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2141,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | v1_relat_1(sK8) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1944]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2142,plain,
% 3.35/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.35/0.99      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.35/0.99      | v1_relat_1(sK8) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2141]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3148,plain,
% 3.35/0.99      ( sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_3144,c_42,c_44,c_2142,c_2174]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3152,plain,
% 3.35/0.99      ( sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK7,sK8),sK5) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2368,c_3148]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_32,negated_conjecture,
% 3.35/0.99      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1567,plain,
% 3.35/0.99      ( k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0)
% 3.35/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3518,plain,
% 3.35/0.99      ( k1_funct_1(sK7,sK4(sK7,sK8)) = k1_funct_1(sK8,sK4(sK7,sK8))
% 3.35/0.99      | sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3152,c_1567]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_19,plain,
% 3.35/0.99      ( ~ v1_funct_1(X0)
% 3.35/0.99      | ~ v1_funct_1(X1)
% 3.35/0.99      | ~ v1_relat_1(X1)
% 3.35/0.99      | ~ v1_relat_1(X0)
% 3.35/0.99      | X0 = X1
% 3.35/0.99      | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
% 3.35/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1571,plain,
% 3.35/0.99      ( X0 = X1
% 3.35/0.99      | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
% 3.35/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.35/0.99      | v1_funct_1(X1) != iProver_top
% 3.35/0.99      | v1_funct_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(X0) != iProver_top
% 3.35/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3632,plain,
% 3.35/0.99      ( k1_relat_1(sK7) != k1_relat_1(sK8)
% 3.35/0.99      | sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0
% 3.35/0.99      | v1_funct_1(sK8) != iProver_top
% 3.35/0.99      | v1_funct_1(sK7) != iProver_top
% 3.35/0.99      | v1_relat_1(sK8) != iProver_top
% 3.35/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3518,c_1571]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3633,plain,
% 3.35/0.99      ( ~ v1_funct_1(sK8)
% 3.35/0.99      | ~ v1_funct_1(sK7)
% 3.35/0.99      | ~ v1_relat_1(sK8)
% 3.35/0.99      | ~ v1_relat_1(sK7)
% 3.35/0.99      | k1_relat_1(sK7) != k1_relat_1(sK8)
% 3.35/0.99      | sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3632]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5355,plain,
% 3.35/0.99      ( k1_relat_1(sK7) != k1_relat_1(sK8)
% 3.35/0.99      | sK8 = sK7
% 3.35/0.99      | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_3632,c_39,c_41,c_42,c_44,c_2142,c_2174,c_3006]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5357,plain,
% 3.35/0.99      ( k1_relat_1(sK7) != sK5 | sK8 = sK7 | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2340,c_5355]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5460,plain,
% 3.35/0.99      ( sK8 = sK7 | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_5357,c_2368]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_24,plain,
% 3.35/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.35/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.35/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_31,negated_conjecture,
% 3.35/0.99      ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
% 3.35/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_401,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | sK8 != X3
% 3.35/0.99      | sK7 != X3
% 3.35/0.99      | sK6 != X2
% 3.35/0.99      | sK5 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_402,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | sK7 != sK8 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_406,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | sK7 != sK8 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_402,c_33]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1562,plain,
% 3.35/0.99      ( sK7 != sK8
% 3.35/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5470,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0
% 3.35/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_5460,c_1562]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5481,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1579,c_5470]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1584,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.35/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.35/0.99      | ~ r2_hidden(X2,X0)
% 3.35/0.99      | r2_hidden(X2,X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1580,plain,
% 3.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.35/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.35/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3902,plain,
% 3.35/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.35/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1564,c_1580]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_0,plain,
% 3.35/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1585,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.35/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4121,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK5,sK6)),sK7) != iProver_top
% 3.35/0.99      | r1_tarski(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3902,c_1585]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4687,plain,
% 3.35/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1584,c_4121]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5573,plain,
% 3.35/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_5481,c_4687]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5,plain,
% 3.35/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5623,plain,
% 3.35/0.99      ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_5573,c_5]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3901,plain,
% 3.35/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.35/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1566,c_1580]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4031,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK5,sK6)),sK8) != iProver_top
% 3.35/0.99      | r1_tarski(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3901,c_1585]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4684,plain,
% 3.35/0.99      ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_1584,c_4031]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5574,plain,
% 3.35/0.99      ( r1_tarski(sK8,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_5481,c_4684]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5622,plain,
% 3.35/0.99      ( r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_5574,c_5]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5312,plain,
% 3.35/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.35/0.99      | sK7 != sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_406]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4,plain,
% 3.35/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2881,plain,
% 3.35/0.99      ( ~ r1_tarski(sK7,k1_xboole_0) | k1_xboole_0 = sK7 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2882,plain,
% 3.35/0.99      ( k1_xboole_0 = sK7 | r1_tarski(sK7,k1_xboole_0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2881]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2873,plain,
% 3.35/0.99      ( ~ r1_tarski(sK8,k1_xboole_0) | k1_xboole_0 = sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2874,plain,
% 3.35/0.99      ( k1_xboole_0 = sK8 | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2873]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1069,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2202,plain,
% 3.35/0.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2601,plain,
% 3.35/0.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2602,plain,
% 3.35/0.99      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2601]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1068,plain,( X0 = X0 ),theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2579,plain,
% 3.35/0.99      ( sK7 = sK7 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2133,plain,
% 3.35/0.99      ( sK8 = sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1781,plain,
% 3.35/0.99      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1960,plain,
% 3.35/0.99      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1781]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1961,plain,
% 3.35/0.99      ( sK8 != sK8 | sK8 = k1_xboole_0 | k1_xboole_0 != sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1960]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1671,plain,
% 3.35/0.99      ( sK8 != X0 | sK7 != X0 | sK7 = sK8 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1672,plain,
% 3.35/0.99      ( sK8 != k1_xboole_0 | sK7 = sK8 | sK7 != k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(contradiction,plain,
% 3.35/0.99      ( $false ),
% 3.35/0.99      inference(minisat,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_5623,c_5622,c_5312,c_2882,c_2874,c_2602,c_2579,c_2133,
% 3.35/0.99                 c_1961,c_1672,c_33]) ).
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  ------                               Statistics
% 3.35/0.99  
% 3.35/0.99  ------ General
% 3.35/0.99  
% 3.35/0.99  abstr_ref_over_cycles:                  0
% 3.35/0.99  abstr_ref_under_cycles:                 0
% 3.35/0.99  gc_basic_clause_elim:                   0
% 3.35/0.99  forced_gc_time:                         0
% 3.35/0.99  parsing_time:                           0.01
% 3.35/0.99  unif_index_cands_time:                  0.
% 3.35/0.99  unif_index_add_time:                    0.
% 3.35/0.99  orderings_time:                         0.
% 3.35/0.99  out_proof_time:                         0.01
% 3.35/0.99  total_time:                             0.206
% 3.35/0.99  num_of_symbols:                         55
% 3.35/0.99  num_of_terms:                           5454
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing
% 3.35/0.99  
% 3.35/0.99  num_of_splits:                          0
% 3.35/0.99  num_of_split_atoms:                     0
% 3.35/0.99  num_of_reused_defs:                     0
% 3.35/0.99  num_eq_ax_congr_red:                    37
% 3.35/0.99  num_of_sem_filtered_clauses:            1
% 3.35/0.99  num_of_subtypes:                        0
% 3.35/0.99  monotx_restored_types:                  0
% 3.35/0.99  sat_num_of_epr_types:                   0
% 3.35/0.99  sat_num_of_non_cyclic_types:            0
% 3.35/0.99  sat_guarded_non_collapsed_types:        0
% 3.35/0.99  num_pure_diseq_elim:                    0
% 3.35/0.99  simp_replaced_by:                       0
% 3.35/0.99  res_preprocessed:                       166
% 3.35/0.99  prep_upred:                             0
% 3.35/0.99  prep_unflattend:                        85
% 3.35/0.99  smt_new_axioms:                         0
% 3.35/0.99  pred_elim_cands:                        5
% 3.35/0.99  pred_elim:                              3
% 3.35/0.99  pred_elim_cl:                           5
% 3.35/0.99  pred_elim_cycles:                       6
% 3.35/0.99  merged_defs:                            0
% 3.35/0.99  merged_defs_ncl:                        0
% 3.35/0.99  bin_hyper_res:                          0
% 3.35/0.99  prep_cycles:                            4
% 3.35/0.99  pred_elim_time:                         0.01
% 3.35/0.99  splitting_time:                         0.
% 3.35/0.99  sem_filter_time:                        0.
% 3.35/0.99  monotx_time:                            0.001
% 3.35/0.99  subtype_inf_time:                       0.
% 3.35/0.99  
% 3.35/0.99  ------ Problem properties
% 3.35/0.99  
% 3.35/0.99  clauses:                                34
% 3.35/0.99  conjectures:                            5
% 3.35/0.99  epr:                                    6
% 3.35/0.99  horn:                                   26
% 3.35/0.99  ground:                                 10
% 3.35/0.99  unary:                                  9
% 3.35/0.99  binary:                                 11
% 3.35/0.99  lits:                                   83
% 3.35/0.99  lits_eq:                                30
% 3.35/0.99  fd_pure:                                0
% 3.35/0.99  fd_pseudo:                              0
% 3.35/0.99  fd_cond:                                2
% 3.35/0.99  fd_pseudo_cond:                         4
% 3.35/0.99  ac_symbols:                             0
% 3.35/0.99  
% 3.35/0.99  ------ Propositional Solver
% 3.35/0.99  
% 3.35/0.99  prop_solver_calls:                      30
% 3.35/0.99  prop_fast_solver_calls:                 1216
% 3.35/0.99  smt_solver_calls:                       0
% 3.35/0.99  smt_fast_solver_calls:                  0
% 3.35/0.99  prop_num_of_clauses:                    2160
% 3.35/0.99  prop_preprocess_simplified:             7075
% 3.35/0.99  prop_fo_subsumed:                       32
% 3.35/0.99  prop_solver_time:                       0.
% 3.35/0.99  smt_solver_time:                        0.
% 3.35/0.99  smt_fast_solver_time:                   0.
% 3.35/0.99  prop_fast_solver_time:                  0.
% 3.35/0.99  prop_unsat_core_time:                   0.
% 3.35/0.99  
% 3.35/0.99  ------ QBF
% 3.35/0.99  
% 3.35/0.99  qbf_q_res:                              0
% 3.35/0.99  qbf_num_tautologies:                    0
% 3.35/0.99  qbf_prep_cycles:                        0
% 3.35/0.99  
% 3.35/0.99  ------ BMC1
% 3.35/0.99  
% 3.35/0.99  bmc1_current_bound:                     -1
% 3.35/0.99  bmc1_last_solved_bound:                 -1
% 3.35/0.99  bmc1_unsat_core_size:                   -1
% 3.35/0.99  bmc1_unsat_core_parents_size:           -1
% 3.35/0.99  bmc1_merge_next_fun:                    0
% 3.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation
% 3.35/0.99  
% 3.35/0.99  inst_num_of_clauses:                    613
% 3.35/0.99  inst_num_in_passive:                    229
% 3.35/0.99  inst_num_in_active:                     295
% 3.35/0.99  inst_num_in_unprocessed:                89
% 3.35/0.99  inst_num_of_loops:                      470
% 3.35/0.99  inst_num_of_learning_restarts:          0
% 3.35/0.99  inst_num_moves_active_passive:          171
% 3.35/0.99  inst_lit_activity:                      0
% 3.35/0.99  inst_lit_activity_moves:                0
% 3.35/0.99  inst_num_tautologies:                   0
% 3.35/0.99  inst_num_prop_implied:                  0
% 3.35/0.99  inst_num_existing_simplified:           0
% 3.35/0.99  inst_num_eq_res_simplified:             0
% 3.35/0.99  inst_num_child_elim:                    0
% 3.35/0.99  inst_num_of_dismatching_blockings:      317
% 3.35/0.99  inst_num_of_non_proper_insts:           916
% 3.35/0.99  inst_num_of_duplicates:                 0
% 3.35/0.99  inst_inst_num_from_inst_to_res:         0
% 3.35/0.99  inst_dismatching_checking_time:         0.
% 3.35/0.99  
% 3.35/0.99  ------ Resolution
% 3.35/0.99  
% 3.35/0.99  res_num_of_clauses:                     0
% 3.35/0.99  res_num_in_passive:                     0
% 3.35/0.99  res_num_in_active:                      0
% 3.35/0.99  res_num_of_loops:                       170
% 3.35/0.99  res_forward_subset_subsumed:            50
% 3.35/0.99  res_backward_subset_subsumed:           0
% 3.35/0.99  res_forward_subsumed:                   0
% 3.35/0.99  res_backward_subsumed:                  3
% 3.35/0.99  res_forward_subsumption_resolution:     0
% 3.35/0.99  res_backward_subsumption_resolution:    0
% 3.35/0.99  res_clause_to_clause_subsumption:       362
% 3.35/0.99  res_orphan_elimination:                 0
% 3.35/0.99  res_tautology_del:                      71
% 3.35/0.99  res_num_eq_res_simplified:              0
% 3.35/0.99  res_num_sel_changes:                    0
% 3.35/0.99  res_moves_from_active_to_pass:          0
% 3.35/0.99  
% 3.35/0.99  ------ Superposition
% 3.35/0.99  
% 3.35/0.99  sup_time_total:                         0.
% 3.35/0.99  sup_time_generating:                    0.
% 3.35/0.99  sup_time_sim_full:                      0.
% 3.35/0.99  sup_time_sim_immed:                     0.
% 3.35/0.99  
% 3.35/0.99  sup_num_of_clauses:                     111
% 3.35/0.99  sup_num_in_active:                      47
% 3.35/0.99  sup_num_in_passive:                     64
% 3.35/0.99  sup_num_of_loops:                       92
% 3.35/0.99  sup_fw_superposition:                   77
% 3.35/0.99  sup_bw_superposition:                   66
% 3.35/0.99  sup_immediate_simplified:               37
% 3.35/0.99  sup_given_eliminated:                   0
% 3.35/0.99  comparisons_done:                       0
% 3.35/0.99  comparisons_avoided:                    55
% 3.35/0.99  
% 3.35/0.99  ------ Simplifications
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  sim_fw_subset_subsumed:                 8
% 3.35/0.99  sim_bw_subset_subsumed:                 17
% 3.35/0.99  sim_fw_subsumed:                        4
% 3.35/0.99  sim_bw_subsumed:                        7
% 3.35/0.99  sim_fw_subsumption_res:                 0
% 3.35/0.99  sim_bw_subsumption_res:                 0
% 3.35/0.99  sim_tautology_del:                      2
% 3.35/0.99  sim_eq_tautology_del:                   13
% 3.35/0.99  sim_eq_res_simp:                        2
% 3.35/0.99  sim_fw_demodulated:                     25
% 3.35/0.99  sim_bw_demodulated:                     32
% 3.35/0.99  sim_light_normalised:                   4
% 3.35/0.99  sim_joinable_taut:                      0
% 3.35/0.99  sim_joinable_simp:                      0
% 3.35/0.99  sim_ac_normalised:                      0
% 3.35/0.99  sim_smt_subsumption:                    0
% 3.35/0.99  
%------------------------------------------------------------------------------
