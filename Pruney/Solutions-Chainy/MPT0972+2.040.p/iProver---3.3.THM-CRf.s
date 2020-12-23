%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:16 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  170 (1557 expanded)
%              Number of clauses        :   98 ( 509 expanded)
%              Number of leaves         :   21 ( 377 expanded)
%              Depth                    :   25
%              Number of atoms          :  581 (9412 expanded)
%              Number of equality atoms :  243 (2093 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f54,f53])).

fof(f91,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_495,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_497,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_33])).

cnf(c_1200,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1202,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2072,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1200,c_1202])).

cnf(c_2213,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_497,c_2072])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_506,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_508,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_36])).

cnf(c_1198,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2073,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1198,c_1202])).

cnf(c_2266,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_508,c_2073])).

cnf(c_19,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1204,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3320,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_1204])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1875,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2366,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_2367,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3076,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3077,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3076])).

cnf(c_4238,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_42,c_44,c_2367,c_3077])).

cnf(c_4239,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4238])).

cnf(c_4251,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_4239])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1880,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2380,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2381,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_4322,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4251,c_39,c_41,c_2381,c_3077])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_16])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_1593,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1196])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1213,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3510,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1593,c_1213])).

cnf(c_3762,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_44,c_2367,c_3077])).

cnf(c_3763,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3762])).

cnf(c_4331,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4322,c_3763])).

cnf(c_23,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_393,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_714,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1617,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_715,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1478,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_6139,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_11638,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4331,c_33,c_393,c_1617,c_6139])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1201,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11645,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = k1_funct_1(sK5,sK2(sK6,sK5))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11638,c_1201])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1205,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11801,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11645,c_1205])).

cnf(c_11802,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11801])).

cnf(c_11804,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11801,c_38,c_36,c_35,c_33,c_393,c_1617,c_2366,c_2380,c_3076,c_6139,c_11802])).

cnf(c_11808,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2213,c_11804])).

cnf(c_11959,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11808,c_2266])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2648,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1203])).

cnf(c_11989,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11959,c_2648])).

cnf(c_2649,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1203])).

cnf(c_11988,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11959,c_2649])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3711,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9421,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3711])).

cnf(c_9422,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9421])).

cnf(c_3639,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3640,plain,
    ( r2_hidden(sK1(sK6,sK5),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3639])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1806,plain,
    ( r1_tarski(X0,sK6)
    | r2_hidden(sK1(X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2599,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK1(sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2600,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1558,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1887,plain,
    ( ~ r1_tarski(sK6,sK5)
    | ~ r1_tarski(sK5,sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_1888,plain,
    ( sK6 = sK5
    | r1_tarski(sK6,sK5) != iProver_top
    | r1_tarski(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1887])).

cnf(c_1622,plain,
    ( r1_tarski(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1626,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_111,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11989,c_11988,c_9422,c_6139,c_3640,c_2600,c_1888,c_1626,c_1617,c_393,c_111,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.99  
% 3.67/0.99  ------  iProver source info
% 3.67/0.99  
% 3.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.99  git: non_committed_changes: false
% 3.67/0.99  git: last_make_outside_of_git: false
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    --mode clausify
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         false
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     num_symb
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       true
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     false
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   []
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_full_bw                           [BwDemod]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  ------ Parsing...
% 3.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.99  ------ Proving...
% 3.67/0.99  ------ Problem Properties 
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  clauses                                 32
% 3.67/0.99  conjectures                             5
% 3.67/0.99  EPR                                     8
% 3.67/0.99  Horn                                    24
% 3.67/0.99  unary                                   11
% 3.67/0.99  binary                                  8
% 3.67/0.99  lits                                    76
% 3.67/0.99  lits eq                                 28
% 3.67/0.99  fd_pure                                 0
% 3.67/0.99  fd_pseudo                               0
% 3.67/0.99  fd_cond                                 1
% 3.67/0.99  fd_pseudo_cond                          3
% 3.67/0.99  AC symbols                              0
% 3.67/0.99  
% 3.67/0.99  ------ Schedule dynamic 5 is on 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  Current options:
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    --mode clausify
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         false
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     none
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       false
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     false
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   []
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_full_bw                           [BwDemod]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ Proving...
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS status Theorem for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  fof(f16,axiom,(
% 3.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f32,plain,(
% 3.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.99    inference(ennf_transformation,[],[f16])).
% 3.67/0.99  
% 3.67/0.99  fof(f33,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.99    inference(flattening,[],[f32])).
% 3.67/0.99  
% 3.67/0.99  fof(f52,plain,(
% 3.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(nnf_transformation,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f81,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f52])).
% 3.67/1.00  
% 3.67/1.00  fof(f17,conjecture,(
% 3.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f18,negated_conjecture,(
% 3.67/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.67/1.00    inference(negated_conjecture,[],[f17])).
% 3.67/1.00  
% 3.67/1.00  fof(f34,plain,(
% 3.67/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.67/1.00    inference(ennf_transformation,[],[f18])).
% 3.67/1.00  
% 3.67/1.00  fof(f35,plain,(
% 3.67/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.67/1.00    inference(flattening,[],[f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f54,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f53,plain,(
% 3.67/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f55,plain,(
% 3.67/1.00    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f54,f53])).
% 3.67/1.00  
% 3.67/1.00  fof(f91,plain,(
% 3.67/1.00    v1_funct_2(sK6,sK3,sK4)),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f92,plain,(
% 3.67/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f14,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f14])).
% 3.67/1.00  
% 3.67/1.00  fof(f78,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f29])).
% 3.67/1.00  
% 3.67/1.00  fof(f88,plain,(
% 3.67/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f89,plain,(
% 3.67/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f11,axiom,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f25,plain,(
% 3.67/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f26,plain,(
% 3.67/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f49,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f50,plain,(
% 3.67/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f49])).
% 3.67/1.00  
% 3.67/1.00  fof(f74,plain,(
% 3.67/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f50])).
% 3.67/1.00  
% 3.67/1.00  fof(f90,plain,(
% 3.67/1.00    v1_funct_1(sK6)),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f8,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f23,plain,(
% 3.67/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f70,plain,(
% 3.67/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f10,axiom,(
% 3.67/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f73,plain,(
% 3.67/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f87,plain,(
% 3.67/1.00    v1_funct_1(sK5)),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f12,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f19,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.67/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.67/1.00  
% 3.67/1.00  fof(f27,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f19])).
% 3.67/1.00  
% 3.67/1.00  fof(f76,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f27])).
% 3.67/1.00  
% 3.67/1.00  fof(f9,axiom,(
% 3.67/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f24,plain,(
% 3.67/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.67/1.00    inference(ennf_transformation,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f48,plain,(
% 3.67/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f71,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f48])).
% 3.67/1.00  
% 3.67/1.00  fof(f2,axiom,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f20,plain,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f2])).
% 3.67/1.00  
% 3.67/1.00  fof(f40,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(nnf_transformation,[],[f20])).
% 3.67/1.00  
% 3.67/1.00  fof(f41,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(rectify,[],[f40])).
% 3.67/1.00  
% 3.67/1.00  fof(f42,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f43,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.67/1.00  
% 3.67/1.00  fof(f58,plain,(
% 3.67/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f43])).
% 3.67/1.00  
% 3.67/1.00  fof(f15,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f30,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.67/1.00    inference(ennf_transformation,[],[f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f31,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(flattening,[],[f30])).
% 3.67/1.00  
% 3.67/1.00  fof(f51,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(nnf_transformation,[],[f31])).
% 3.67/1.00  
% 3.67/1.00  fof(f80,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f51])).
% 3.67/1.00  
% 3.67/1.00  fof(f99,plain,(
% 3.67/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(equality_resolution,[],[f80])).
% 3.67/1.00  
% 3.67/1.00  fof(f94,plain,(
% 3.67/1.00    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f93,plain,(
% 3.67/1.00    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f75,plain,(
% 3.67/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f50])).
% 3.67/1.00  
% 3.67/1.00  fof(f13,axiom,(
% 3.67/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f13])).
% 3.67/1.00  
% 3.67/1.00  fof(f77,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f36,plain,(
% 3.67/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.67/1.00    inference(nnf_transformation,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f37,plain,(
% 3.67/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/1.00    inference(rectify,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f38,plain,(
% 3.67/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f39,plain,(
% 3.67/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.67/1.00  
% 3.67/1.00  fof(f56,plain,(
% 3.67/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f39])).
% 3.67/1.00  
% 3.67/1.00  fof(f59,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f43])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f44,plain,(
% 3.67/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f45,plain,(
% 3.67/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.00    inference(flattening,[],[f44])).
% 3.67/1.00  
% 3.67/1.00  fof(f64,plain,(
% 3.67/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f45])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    v1_xboole_0(k1_xboole_0)),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f61,plain,(
% 3.67/1.00    v1_xboole_0(k1_xboole_0)),
% 3.67/1.00    inference(cnf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_30,plain,
% 3.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.67/1.00      | k1_xboole_0 = X2 ),
% 3.67/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_34,negated_conjecture,
% 3.67/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.67/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_494,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.67/1.00      | sK6 != X0
% 3.67/1.00      | sK4 != X2
% 3.67/1.00      | sK3 != X1
% 3.67/1.00      | k1_xboole_0 = X2 ),
% 3.67/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_495,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.67/1.00      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.67/1.00      | k1_xboole_0 = sK4 ),
% 3.67/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_33,negated_conjecture,
% 3.67/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_497,plain,
% 3.67/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_495,c_33]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1200,plain,
% 3.67/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_22,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1202,plain,
% 3.67/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.67/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2072,plain,
% 3.67/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1200,c_1202]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2213,plain,
% 3.67/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_497,c_2072]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_37,negated_conjecture,
% 3.67/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.67/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_505,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.67/1.00      | sK5 != X0
% 3.67/1.00      | sK4 != X2
% 3.67/1.00      | sK3 != X1
% 3.67/1.00      | k1_xboole_0 = X2 ),
% 3.67/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_506,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.67/1.00      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.67/1.00      | k1_xboole_0 = sK4 ),
% 3.67/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_36,negated_conjecture,
% 3.67/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_508,plain,
% 3.67/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_506,c_36]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1198,plain,
% 3.67/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2073,plain,
% 3.67/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1198,c_1202]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2266,plain,
% 3.67/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_508,c_2073]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_19,plain,
% 3.67/1.00      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.67/1.00      | ~ v1_funct_1(X1)
% 3.67/1.00      | ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X1)
% 3.67/1.00      | X1 = X0
% 3.67/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1204,plain,
% 3.67/1.00      ( X0 = X1
% 3.67/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.67/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_funct_1(X1) != iProver_top
% 3.67/1.00      | v1_relat_1(X1) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3320,plain,
% 3.67/1.00      ( k1_relat_1(X0) != sK3
% 3.67/1.00      | sK6 = X0
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_funct_1(sK6) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2213,c_1204]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_35,negated_conjecture,
% 3.67/1.00      ( v1_funct_1(sK6) ),
% 3.67/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_42,plain,
% 3.67/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_44,plain,
% 3.67/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/1.00      | ~ v1_relat_1(X1)
% 3.67/1.00      | v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1875,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | v1_relat_1(sK6) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2366,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.67/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.67/1.00      | v1_relat_1(sK6) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1875]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2367,plain,
% 3.67/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.67/1.00      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.67/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17,plain,
% 3.67/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3076,plain,
% 3.67/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3077,plain,
% 3.67/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3076]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4238,plain,
% 3.67/1.00      ( v1_relat_1(X0) != iProver_top
% 3.67/1.00      | k1_relat_1(X0) != sK3
% 3.67/1.00      | sK6 = X0
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_3320,c_42,c_44,c_2367,c_3077]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4239,plain,
% 3.67/1.00      ( k1_relat_1(X0) != sK3
% 3.67/1.00      | sK6 = X0
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_4238]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4251,plain,
% 3.67/1.00      ( sK6 = sK5
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 3.67/1.00      | v1_funct_1(sK5) != iProver_top
% 3.67/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2266,c_4239]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_38,negated_conjecture,
% 3.67/1.00      ( v1_funct_1(sK5) ),
% 3.67/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_39,plain,
% 3.67/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_41,plain,
% 3.67/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1880,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | v1_relat_1(sK5) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2380,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.67/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.67/1.00      | v1_relat_1(sK5) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1880]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2381,plain,
% 3.67/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.67/1.00      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.67/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4322,plain,
% 3.67/1.00      ( sK6 = sK5
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_4251,c_39,c_41,c_2381,c_3077]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_20,plain,
% 3.67/1.00      ( v4_relat_1(X0,X1)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16,plain,
% 3.67/1.00      ( ~ v4_relat_1(X0,X1)
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.67/1.00      | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_401,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.67/1.00      | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_20,c_16]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1196,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1593,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
% 3.67/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1200,c_1196]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1213,plain,
% 3.67/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.67/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3510,plain,
% 3.67/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.67/1.00      | r2_hidden(X0,sK3) = iProver_top
% 3.67/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1593,c_1213]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3762,plain,
% 3.67/1.00      ( r2_hidden(X0,sK3) = iProver_top
% 3.67/1.00      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_3510,c_44,c_2367,c_3077]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3763,plain,
% 3.67/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.67/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_3762]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4331,plain,
% 3.67/1.00      ( sK6 = sK5
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4322,c_3763]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_23,plain,
% 3.67/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_31,negated_conjecture,
% 3.67/1.00      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.67/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_392,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | sK6 != X0
% 3.67/1.00      | sK5 != X0
% 3.67/1.00      | sK4 != X2
% 3.67/1.00      | sK3 != X1 ),
% 3.67/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_393,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.67/1.00      | sK5 != sK6 ),
% 3.67/1.00      inference(unflattening,[status(thm)],[c_392]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_714,plain,( X0 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1617,plain,
% 3.67/1.00      ( sK5 = sK5 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_714]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_715,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1478,plain,
% 3.67/1.00      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_715]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6139,plain,
% 3.67/1.00      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11638,plain,
% 3.67/1.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_4331,c_33,c_393,c_1617,c_6139]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_32,negated_conjecture,
% 3.67/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1201,plain,
% 3.67/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 3.67/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11645,plain,
% 3.67/1.00      ( k1_funct_1(sK6,sK2(sK6,sK5)) = k1_funct_1(sK5,sK2(sK6,sK5))
% 3.67/1.00      | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_11638,c_1201]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_18,plain,
% 3.67/1.00      ( ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v1_funct_1(X1)
% 3.67/1.00      | ~ v1_relat_1(X1)
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | X0 = X1
% 3.67/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.67/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1205,plain,
% 3.67/1.00      ( X0 = X1
% 3.67/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.67/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.67/1.00      | v1_funct_1(X1) != iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11801,plain,
% 3.67/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.67/1.00      | sK6 = sK5
% 3.67/1.00      | sK4 = k1_xboole_0
% 3.67/1.00      | v1_funct_1(sK6) != iProver_top
% 3.67/1.00      | v1_funct_1(sK5) != iProver_top
% 3.67/1.00      | v1_relat_1(sK6) != iProver_top
% 3.67/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_11645,c_1205]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11802,plain,
% 3.67/1.00      ( ~ v1_funct_1(sK6)
% 3.67/1.00      | ~ v1_funct_1(sK5)
% 3.67/1.00      | ~ v1_relat_1(sK6)
% 3.67/1.00      | ~ v1_relat_1(sK5)
% 3.67/1.00      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.67/1.00      | sK6 = sK5
% 3.67/1.00      | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11801]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11804,plain,
% 3.67/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_11801,c_38,c_36,c_35,c_33,c_393,c_1617,c_2366,c_2380,
% 3.67/1.00                 c_3076,c_6139,c_11802]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11808,plain,
% 3.67/1.00      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2213,c_11804]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11959,plain,
% 3.67/1.00      ( sK4 = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_11808,c_2266]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_21,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | ~ v1_xboole_0(X2)
% 3.67/1.00      | v1_xboole_0(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1203,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.00      | v1_xboole_0(X2) != iProver_top
% 3.67/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2648,plain,
% 3.67/1.00      ( v1_xboole_0(sK6) = iProver_top
% 3.67/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1200,c_1203]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11989,plain,
% 3.67/1.00      ( v1_xboole_0(sK6) = iProver_top
% 3.67/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_11959,c_2648]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2649,plain,
% 3.67/1.00      ( v1_xboole_0(sK5) = iProver_top
% 3.67/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1198,c_1203]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11988,plain,
% 3.67/1.00      ( v1_xboole_0(sK5) = iProver_top
% 3.67/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_11959,c_2649]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3711,plain,
% 3.67/1.00      ( ~ r2_hidden(sK1(X0,sK6),X0) | ~ v1_xboole_0(X0) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9421,plain,
% 3.67/1.00      ( ~ r2_hidden(sK1(sK5,sK6),sK5) | ~ v1_xboole_0(sK5) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3711]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9422,plain,
% 3.67/1.00      ( r2_hidden(sK1(sK5,sK6),sK5) != iProver_top
% 3.67/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_9421]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3639,plain,
% 3.67/1.00      ( ~ r2_hidden(sK1(sK6,sK5),sK6) | ~ v1_xboole_0(sK6) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3640,plain,
% 3.67/1.00      ( r2_hidden(sK1(sK6,sK5),sK6) != iProver_top
% 3.67/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3639]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3,plain,
% 3.67/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1806,plain,
% 3.67/1.00      ( r1_tarski(X0,sK6) | r2_hidden(sK1(X0,sK6),X0) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2599,plain,
% 3.67/1.00      ( r1_tarski(sK5,sK6) | r2_hidden(sK1(sK5,sK6),sK5) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1806]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2600,plain,
% 3.67/1.00      ( r1_tarski(sK5,sK6) = iProver_top
% 3.67/1.00      | r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1558,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1887,plain,
% 3.67/1.00      ( ~ r1_tarski(sK6,sK5) | ~ r1_tarski(sK5,sK6) | sK6 = sK5 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1558]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1888,plain,
% 3.67/1.00      ( sK6 = sK5
% 3.67/1.00      | r1_tarski(sK6,sK5) != iProver_top
% 3.67/1.00      | r1_tarski(sK5,sK6) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1887]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1622,plain,
% 3.67/1.00      ( r1_tarski(sK6,sK5) | r2_hidden(sK1(sK6,sK5),sK6) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1626,plain,
% 3.67/1.00      ( r1_tarski(sK6,sK5) = iProver_top
% 3.67/1.00      | r2_hidden(sK1(sK6,sK5),sK6) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5,plain,
% 3.67/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_111,plain,
% 3.67/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(contradiction,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(minisat,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_11989,c_11988,c_9422,c_6139,c_3640,c_2600,c_1888,
% 3.67/1.00                 c_1626,c_1617,c_393,c_111,c_33]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ General
% 3.67/1.00  
% 3.67/1.00  abstr_ref_over_cycles:                  0
% 3.67/1.00  abstr_ref_under_cycles:                 0
% 3.67/1.00  gc_basic_clause_elim:                   0
% 3.67/1.00  forced_gc_time:                         0
% 3.67/1.00  parsing_time:                           0.009
% 3.67/1.00  unif_index_cands_time:                  0.
% 3.67/1.00  unif_index_add_time:                    0.
% 3.67/1.00  orderings_time:                         0.
% 3.67/1.00  out_proof_time:                         0.016
% 3.67/1.00  total_time:                             0.475
% 3.67/1.00  num_of_symbols:                         53
% 3.67/1.00  num_of_terms:                           8883
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing
% 3.67/1.00  
% 3.67/1.00  num_of_splits:                          0
% 3.67/1.00  num_of_split_atoms:                     0
% 3.67/1.00  num_of_reused_defs:                     0
% 3.67/1.00  num_eq_ax_congr_red:                    25
% 3.67/1.00  num_of_sem_filtered_clauses:            1
% 3.67/1.00  num_of_subtypes:                        0
% 3.67/1.00  monotx_restored_types:                  0
% 3.67/1.00  sat_num_of_epr_types:                   0
% 3.67/1.00  sat_num_of_non_cyclic_types:            0
% 3.67/1.00  sat_guarded_non_collapsed_types:        0
% 3.67/1.00  num_pure_diseq_elim:                    0
% 3.67/1.00  simp_replaced_by:                       0
% 3.67/1.00  res_preprocessed:                       159
% 3.67/1.00  prep_upred:                             0
% 3.67/1.00  prep_unflattend:                        41
% 3.67/1.00  smt_new_axioms:                         0
% 3.67/1.00  pred_elim_cands:                        6
% 3.67/1.00  pred_elim:                              3
% 3.67/1.00  pred_elim_cl:                           6
% 3.67/1.00  pred_elim_cycles:                       5
% 3.67/1.00  merged_defs:                            0
% 3.67/1.00  merged_defs_ncl:                        0
% 3.67/1.00  bin_hyper_res:                          0
% 3.67/1.00  prep_cycles:                            4
% 3.67/1.00  pred_elim_time:                         0.004
% 3.67/1.00  splitting_time:                         0.
% 3.67/1.00  sem_filter_time:                        0.
% 3.67/1.00  monotx_time:                            0.
% 3.67/1.00  subtype_inf_time:                       0.
% 3.67/1.00  
% 3.67/1.00  ------ Problem properties
% 3.67/1.00  
% 3.67/1.00  clauses:                                32
% 3.67/1.00  conjectures:                            5
% 3.67/1.00  epr:                                    8
% 3.67/1.00  horn:                                   24
% 3.67/1.00  ground:                                 12
% 3.67/1.00  unary:                                  11
% 3.67/1.00  binary:                                 8
% 3.67/1.00  lits:                                   76
% 3.67/1.00  lits_eq:                                28
% 3.67/1.00  fd_pure:                                0
% 3.67/1.00  fd_pseudo:                              0
% 3.67/1.00  fd_cond:                                1
% 3.67/1.00  fd_pseudo_cond:                         3
% 3.67/1.00  ac_symbols:                             0
% 3.67/1.00  
% 3.67/1.00  ------ Propositional Solver
% 3.67/1.00  
% 3.67/1.00  prop_solver_calls:                      29
% 3.67/1.00  prop_fast_solver_calls:                 1371
% 3.67/1.00  smt_solver_calls:                       0
% 3.67/1.00  smt_fast_solver_calls:                  0
% 3.67/1.00  prop_num_of_clauses:                    4076
% 3.67/1.00  prop_preprocess_simplified:             9648
% 3.67/1.00  prop_fo_subsumed:                       46
% 3.67/1.00  prop_solver_time:                       0.
% 3.67/1.00  smt_solver_time:                        0.
% 3.67/1.00  smt_fast_solver_time:                   0.
% 3.67/1.00  prop_fast_solver_time:                  0.
% 3.67/1.00  prop_unsat_core_time:                   0.
% 3.67/1.00  
% 3.67/1.00  ------ QBF
% 3.67/1.00  
% 3.67/1.00  qbf_q_res:                              0
% 3.67/1.00  qbf_num_tautologies:                    0
% 3.67/1.00  qbf_prep_cycles:                        0
% 3.67/1.00  
% 3.67/1.00  ------ BMC1
% 3.67/1.00  
% 3.67/1.00  bmc1_current_bound:                     -1
% 3.67/1.00  bmc1_last_solved_bound:                 -1
% 3.67/1.00  bmc1_unsat_core_size:                   -1
% 3.67/1.00  bmc1_unsat_core_parents_size:           -1
% 3.67/1.00  bmc1_merge_next_fun:                    0
% 3.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation
% 3.67/1.00  
% 3.67/1.00  inst_num_of_clauses:                    1373
% 3.67/1.00  inst_num_in_passive:                    98
% 3.67/1.00  inst_num_in_active:                     652
% 3.67/1.00  inst_num_in_unprocessed:                623
% 3.67/1.00  inst_num_of_loops:                      830
% 3.67/1.00  inst_num_of_learning_restarts:          0
% 3.67/1.00  inst_num_moves_active_passive:          175
% 3.67/1.00  inst_lit_activity:                      0
% 3.67/1.00  inst_lit_activity_moves:                0
% 3.67/1.00  inst_num_tautologies:                   0
% 3.67/1.00  inst_num_prop_implied:                  0
% 3.67/1.00  inst_num_existing_simplified:           0
% 3.67/1.00  inst_num_eq_res_simplified:             0
% 3.67/1.00  inst_num_child_elim:                    0
% 3.67/1.00  inst_num_of_dismatching_blockings:      568
% 3.67/1.00  inst_num_of_non_proper_insts:           1509
% 3.67/1.00  inst_num_of_duplicates:                 0
% 3.67/1.00  inst_inst_num_from_inst_to_res:         0
% 3.67/1.00  inst_dismatching_checking_time:         0.
% 3.67/1.00  
% 3.67/1.00  ------ Resolution
% 3.67/1.00  
% 3.67/1.00  res_num_of_clauses:                     0
% 3.67/1.00  res_num_in_passive:                     0
% 3.67/1.00  res_num_in_active:                      0
% 3.67/1.00  res_num_of_loops:                       163
% 3.67/1.00  res_forward_subset_subsumed:            139
% 3.67/1.00  res_backward_subset_subsumed:           4
% 3.67/1.00  res_forward_subsumed:                   0
% 3.67/1.00  res_backward_subsumed:                  0
% 3.67/1.00  res_forward_subsumption_resolution:     0
% 3.67/1.00  res_backward_subsumption_resolution:    0
% 3.67/1.00  res_clause_to_clause_subsumption:       860
% 3.67/1.00  res_orphan_elimination:                 0
% 3.67/1.00  res_tautology_del:                      85
% 3.67/1.00  res_num_eq_res_simplified:              0
% 3.67/1.00  res_num_sel_changes:                    0
% 3.67/1.00  res_moves_from_active_to_pass:          0
% 3.67/1.00  
% 3.67/1.00  ------ Superposition
% 3.67/1.00  
% 3.67/1.00  sup_time_total:                         0.
% 3.67/1.00  sup_time_generating:                    0.
% 3.67/1.00  sup_time_sim_full:                      0.
% 3.67/1.00  sup_time_sim_immed:                     0.
% 3.67/1.00  
% 3.67/1.00  sup_num_of_clauses:                     238
% 3.67/1.00  sup_num_in_active:                      116
% 3.67/1.00  sup_num_in_passive:                     122
% 3.67/1.00  sup_num_of_loops:                       164
% 3.67/1.00  sup_fw_superposition:                   425
% 3.67/1.00  sup_bw_superposition:                   182
% 3.67/1.00  sup_immediate_simplified:               152
% 3.67/1.00  sup_given_eliminated:                   1
% 3.67/1.00  comparisons_done:                       0
% 3.67/1.00  comparisons_avoided:                    195
% 3.67/1.00  
% 3.67/1.00  ------ Simplifications
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  sim_fw_subset_subsumed:                 92
% 3.67/1.00  sim_bw_subset_subsumed:                 11
% 3.67/1.00  sim_fw_subsumed:                        47
% 3.67/1.00  sim_bw_subsumed:                        13
% 3.67/1.00  sim_fw_subsumption_res:                 4
% 3.67/1.00  sim_bw_subsumption_res:                 0
% 3.67/1.00  sim_tautology_del:                      9
% 3.67/1.00  sim_eq_tautology_del:                   95
% 3.67/1.00  sim_eq_res_simp:                        2
% 3.67/1.00  sim_fw_demodulated:                     8
% 3.67/1.00  sim_bw_demodulated:                     38
% 3.67/1.00  sim_light_normalised:                   0
% 3.67/1.00  sim_joinable_taut:                      0
% 3.67/1.00  sim_joinable_simp:                      0
% 3.67/1.00  sim_ac_normalised:                      0
% 3.67/1.00  sim_smt_subsumption:                    0
% 3.67/1.00  
%------------------------------------------------------------------------------
