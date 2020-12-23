%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:09 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  205 (8656 expanded)
%              Number of clauses        :  132 (2492 expanded)
%              Number of leaves         :   21 (2179 expanded)
%              Depth                    :   28
%              Number of atoms          :  688 (56785 expanded)
%              Number of equality atoms :  345 (13299 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f28,f44,f43])).

fof(f77,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f37])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1586,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6045,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_1587,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5596,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK6)) != X0
    | k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK5,sK2(sK5,sK6))
    | k1_funct_1(sK5,sK2(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_6044,plain,
    ( k1_funct_1(sK6,sK2(sK5,sK6)) != k1_funct_1(sK6,sK2(sK5,sK6))
    | k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK5,sK2(sK5,sK6))
    | k1_funct_1(sK5,sK2(sK5,sK6)) != k1_funct_1(sK6,sK2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5596])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5608,plain,
    ( ~ r2_hidden(sK2(sK5,sK6),sK3)
    | k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2654,plain,
    ( r2_hidden(sK2(sK5,sK6),X0)
    | ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
    | ~ r1_tarski(k1_relat_1(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5607,plain,
    ( ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
    | r2_hidden(sK2(sK5,sK6),sK3)
    | ~ r1_tarski(k1_relat_1(sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_903,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_904,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_906,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_27])).

cnf(c_1989,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1991,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2882,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1989,c_1991])).

cnf(c_3214,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_906,c_2882])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_914,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_915,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_917,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_915,c_30])).

cnf(c_1987,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2883,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1987,c_1991])).

cnf(c_3303,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_917,c_2883])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1993,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3482,plain,
    ( k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_1993])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2197,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2198,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2197])).

cnf(c_3848,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3482,c_33,c_35,c_2198])).

cnf(c_3849,plain,
    ( k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3848])).

cnf(c_3860,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3214,c_3849])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X3
    | sK5 != X3
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_27])).

cnf(c_476,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != X0
    | sK1(X0) != X1
    | sK6 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_331])).

cnf(c_477,plain,
    ( sK6 != sK5 ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2195,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_3886,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_36,c_38,c_477,c_2195])).

cnf(c_3892,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_3886])).

cnf(c_1990,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3897,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3892,c_1990])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1994,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3962,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3897,c_1994])).

cnf(c_3979,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3962])).

cnf(c_4448,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3962,c_32,c_30,c_29,c_27,c_477,c_2194,c_2197,c_3979])).

cnf(c_4452,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3214,c_4448])).

cnf(c_4494,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4452,c_3303])).

cnf(c_4510,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4494,c_1987])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4512,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4510,c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2885,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1991])).

cnf(c_4559,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4512,c_2885])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK5 != X0
    | sK4 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_1980,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_2074,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1980,c_8])).

cnf(c_4505,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4494,c_2074])).

cnf(c_4525,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4505,c_4512])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_857,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_1982,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2088,plain,
    ( sK5 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1982,c_7])).

cnf(c_4503,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4494,c_2088])).

cnf(c_4534,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4503])).

cnf(c_4538,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4534,c_4512])).

cnf(c_1588,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2369,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(sK6,sK5)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_2371,plain,
    ( r1_tarski(sK6,sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2369])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2559,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2579,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2461,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3083,plain,
    ( ~ r1_tarski(sK6,sK5)
    | ~ r1_tarski(sK5,sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_2564,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_3281,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK5,sK6)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2564])).

cnf(c_3283,plain,
    ( r1_tarski(sK5,sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK6 != X0
    | sK4 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_842,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_1983,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2097,plain,
    ( sK6 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1983,c_7])).

cnf(c_4502,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4494,c_2097])).

cnf(c_4541,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4502])).

cnf(c_4509,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4494,c_1989])).

cnf(c_4515,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4509,c_7])).

cnf(c_4545,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4541,c_4515])).

cnf(c_5336,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4538,c_477,c_2371,c_2559,c_2579,c_3083,c_3283,c_4545])).

cnf(c_5532,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4525,c_477,c_2371,c_2559,c_2579,c_3083,c_3283,c_4538,c_4545])).

cnf(c_5535,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4559,c_5532])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_12])).

cnf(c_351,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_15])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1984,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_2397,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1984])).

cnf(c_4711,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_2397])).

cnf(c_4722,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4711])).

cnf(c_4297,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4300,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4297])).

cnf(c_2794,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK6))
    | ~ r1_tarski(k1_relat_1(sK6),X0)
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2795,plain,
    ( k1_relat_1(sK6) = X0
    | r1_tarski(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_2797,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2795])).

cnf(c_2672,plain,
    ( k1_relat_1(sK6) != X0
    | k1_relat_1(sK5) != X0
    | k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_2673,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k1_relat_1(sK5) = k1_relat_1(sK6)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_2308,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | X0 = sK5
    | k1_funct_1(X0,sK2(sK5,X0)) != k1_funct_1(sK5,sK2(sK5,X0))
    | k1_relat_1(sK5) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2622,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK6,sK2(sK5,sK6)) != k1_funct_1(sK5,sK2(sK5,sK6))
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_2313,plain,
    ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | X0 = sK5
    | k1_relat_1(sK5) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2616,plain,
    ( r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_2219,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | r1_tarski(k1_relat_1(sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6045,c_6044,c_5608,c_5607,c_5535,c_4722,c_4300,c_2797,c_2673,c_2622,c_2616,c_2219,c_2197,c_2194,c_477,c_27,c_29,c_30,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.25/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/1.02  
% 3.25/1.02  ------  iProver source info
% 3.25/1.02  
% 3.25/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.25/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/1.02  git: non_committed_changes: false
% 3.25/1.02  git: last_make_outside_of_git: false
% 3.25/1.02  
% 3.25/1.02  ------ 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options
% 3.25/1.02  
% 3.25/1.02  --out_options                           all
% 3.25/1.02  --tptp_safe_out                         true
% 3.25/1.02  --problem_path                          ""
% 3.25/1.02  --include_path                          ""
% 3.25/1.02  --clausifier                            res/vclausify_rel
% 3.25/1.02  --clausifier_options                    --mode clausify
% 3.25/1.02  --stdin                                 false
% 3.25/1.02  --stats_out                             all
% 3.25/1.02  
% 3.25/1.02  ------ General Options
% 3.25/1.02  
% 3.25/1.02  --fof                                   false
% 3.25/1.02  --time_out_real                         305.
% 3.25/1.02  --time_out_virtual                      -1.
% 3.25/1.02  --symbol_type_check                     false
% 3.25/1.02  --clausify_out                          false
% 3.25/1.02  --sig_cnt_out                           false
% 3.25/1.02  --trig_cnt_out                          false
% 3.25/1.02  --trig_cnt_out_tolerance                1.
% 3.25/1.02  --trig_cnt_out_sk_spl                   false
% 3.25/1.02  --abstr_cl_out                          false
% 3.25/1.02  
% 3.25/1.02  ------ Global Options
% 3.25/1.02  
% 3.25/1.02  --schedule                              default
% 3.25/1.02  --add_important_lit                     false
% 3.25/1.02  --prop_solver_per_cl                    1000
% 3.25/1.02  --min_unsat_core                        false
% 3.25/1.02  --soft_assumptions                      false
% 3.25/1.02  --soft_lemma_size                       3
% 3.25/1.02  --prop_impl_unit_size                   0
% 3.25/1.02  --prop_impl_unit                        []
% 3.25/1.02  --share_sel_clauses                     true
% 3.25/1.02  --reset_solvers                         false
% 3.25/1.02  --bc_imp_inh                            [conj_cone]
% 3.25/1.02  --conj_cone_tolerance                   3.
% 3.25/1.02  --extra_neg_conj                        none
% 3.25/1.02  --large_theory_mode                     true
% 3.25/1.02  --prolific_symb_bound                   200
% 3.25/1.02  --lt_threshold                          2000
% 3.25/1.02  --clause_weak_htbl                      true
% 3.25/1.02  --gc_record_bc_elim                     false
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing Options
% 3.25/1.02  
% 3.25/1.02  --preprocessing_flag                    true
% 3.25/1.02  --time_out_prep_mult                    0.1
% 3.25/1.02  --splitting_mode                        input
% 3.25/1.02  --splitting_grd                         true
% 3.25/1.02  --splitting_cvd                         false
% 3.25/1.02  --splitting_cvd_svl                     false
% 3.25/1.02  --splitting_nvd                         32
% 3.25/1.02  --sub_typing                            true
% 3.25/1.02  --prep_gs_sim                           true
% 3.25/1.02  --prep_unflatten                        true
% 3.25/1.02  --prep_res_sim                          true
% 3.25/1.02  --prep_upred                            true
% 3.25/1.02  --prep_sem_filter                       exhaustive
% 3.25/1.02  --prep_sem_filter_out                   false
% 3.25/1.02  --pred_elim                             true
% 3.25/1.02  --res_sim_input                         true
% 3.25/1.02  --eq_ax_congr_red                       true
% 3.25/1.02  --pure_diseq_elim                       true
% 3.25/1.02  --brand_transform                       false
% 3.25/1.02  --non_eq_to_eq                          false
% 3.25/1.02  --prep_def_merge                        true
% 3.25/1.02  --prep_def_merge_prop_impl              false
% 3.25/1.02  --prep_def_merge_mbd                    true
% 3.25/1.02  --prep_def_merge_tr_red                 false
% 3.25/1.02  --prep_def_merge_tr_cl                  false
% 3.25/1.02  --smt_preprocessing                     true
% 3.25/1.02  --smt_ac_axioms                         fast
% 3.25/1.02  --preprocessed_out                      false
% 3.25/1.02  --preprocessed_stats                    false
% 3.25/1.02  
% 3.25/1.02  ------ Abstraction refinement Options
% 3.25/1.02  
% 3.25/1.02  --abstr_ref                             []
% 3.25/1.02  --abstr_ref_prep                        false
% 3.25/1.02  --abstr_ref_until_sat                   false
% 3.25/1.02  --abstr_ref_sig_restrict                funpre
% 3.25/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.02  --abstr_ref_under                       []
% 3.25/1.02  
% 3.25/1.02  ------ SAT Options
% 3.25/1.02  
% 3.25/1.02  --sat_mode                              false
% 3.25/1.02  --sat_fm_restart_options                ""
% 3.25/1.02  --sat_gr_def                            false
% 3.25/1.02  --sat_epr_types                         true
% 3.25/1.02  --sat_non_cyclic_types                  false
% 3.25/1.02  --sat_finite_models                     false
% 3.25/1.02  --sat_fm_lemmas                         false
% 3.25/1.02  --sat_fm_prep                           false
% 3.25/1.02  --sat_fm_uc_incr                        true
% 3.25/1.02  --sat_out_model                         small
% 3.25/1.02  --sat_out_clauses                       false
% 3.25/1.02  
% 3.25/1.02  ------ QBF Options
% 3.25/1.02  
% 3.25/1.02  --qbf_mode                              false
% 3.25/1.02  --qbf_elim_univ                         false
% 3.25/1.02  --qbf_dom_inst                          none
% 3.25/1.02  --qbf_dom_pre_inst                      false
% 3.25/1.02  --qbf_sk_in                             false
% 3.25/1.02  --qbf_pred_elim                         true
% 3.25/1.02  --qbf_split                             512
% 3.25/1.02  
% 3.25/1.02  ------ BMC1 Options
% 3.25/1.02  
% 3.25/1.02  --bmc1_incremental                      false
% 3.25/1.02  --bmc1_axioms                           reachable_all
% 3.25/1.02  --bmc1_min_bound                        0
% 3.25/1.02  --bmc1_max_bound                        -1
% 3.25/1.02  --bmc1_max_bound_default                -1
% 3.25/1.02  --bmc1_symbol_reachability              true
% 3.25/1.02  --bmc1_property_lemmas                  false
% 3.25/1.02  --bmc1_k_induction                      false
% 3.25/1.02  --bmc1_non_equiv_states                 false
% 3.25/1.02  --bmc1_deadlock                         false
% 3.25/1.02  --bmc1_ucm                              false
% 3.25/1.02  --bmc1_add_unsat_core                   none
% 3.25/1.02  --bmc1_unsat_core_children              false
% 3.25/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.02  --bmc1_out_stat                         full
% 3.25/1.02  --bmc1_ground_init                      false
% 3.25/1.02  --bmc1_pre_inst_next_state              false
% 3.25/1.02  --bmc1_pre_inst_state                   false
% 3.25/1.02  --bmc1_pre_inst_reach_state             false
% 3.25/1.02  --bmc1_out_unsat_core                   false
% 3.25/1.02  --bmc1_aig_witness_out                  false
% 3.25/1.02  --bmc1_verbose                          false
% 3.25/1.02  --bmc1_dump_clauses_tptp                false
% 3.25/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.02  --bmc1_dump_file                        -
% 3.25/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.02  --bmc1_ucm_extend_mode                  1
% 3.25/1.02  --bmc1_ucm_init_mode                    2
% 3.25/1.02  --bmc1_ucm_cone_mode                    none
% 3.25/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.02  --bmc1_ucm_relax_model                  4
% 3.25/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.02  --bmc1_ucm_layered_model                none
% 3.25/1.02  --bmc1_ucm_max_lemma_size               10
% 3.25/1.02  
% 3.25/1.02  ------ AIG Options
% 3.25/1.02  
% 3.25/1.02  --aig_mode                              false
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation Options
% 3.25/1.02  
% 3.25/1.02  --instantiation_flag                    true
% 3.25/1.02  --inst_sos_flag                         false
% 3.25/1.02  --inst_sos_phase                        true
% 3.25/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel_side                     num_symb
% 3.25/1.02  --inst_solver_per_active                1400
% 3.25/1.02  --inst_solver_calls_frac                1.
% 3.25/1.02  --inst_passive_queue_type               priority_queues
% 3.25/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.02  --inst_passive_queues_freq              [25;2]
% 3.25/1.02  --inst_dismatching                      true
% 3.25/1.02  --inst_eager_unprocessed_to_passive     true
% 3.25/1.02  --inst_prop_sim_given                   true
% 3.25/1.02  --inst_prop_sim_new                     false
% 3.25/1.02  --inst_subs_new                         false
% 3.25/1.02  --inst_eq_res_simp                      false
% 3.25/1.02  --inst_subs_given                       false
% 3.25/1.02  --inst_orphan_elimination               true
% 3.25/1.02  --inst_learning_loop_flag               true
% 3.25/1.02  --inst_learning_start                   3000
% 3.25/1.02  --inst_learning_factor                  2
% 3.25/1.02  --inst_start_prop_sim_after_learn       3
% 3.25/1.02  --inst_sel_renew                        solver
% 3.25/1.02  --inst_lit_activity_flag                true
% 3.25/1.02  --inst_restr_to_given                   false
% 3.25/1.02  --inst_activity_threshold               500
% 3.25/1.02  --inst_out_proof                        true
% 3.25/1.02  
% 3.25/1.02  ------ Resolution Options
% 3.25/1.02  
% 3.25/1.02  --resolution_flag                       true
% 3.25/1.02  --res_lit_sel                           adaptive
% 3.25/1.02  --res_lit_sel_side                      none
% 3.25/1.02  --res_ordering                          kbo
% 3.25/1.02  --res_to_prop_solver                    active
% 3.25/1.02  --res_prop_simpl_new                    false
% 3.25/1.02  --res_prop_simpl_given                  true
% 3.25/1.02  --res_passive_queue_type                priority_queues
% 3.25/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.02  --res_passive_queues_freq               [15;5]
% 3.25/1.02  --res_forward_subs                      full
% 3.25/1.02  --res_backward_subs                     full
% 3.25/1.02  --res_forward_subs_resolution           true
% 3.25/1.02  --res_backward_subs_resolution          true
% 3.25/1.02  --res_orphan_elimination                true
% 3.25/1.02  --res_time_limit                        2.
% 3.25/1.02  --res_out_proof                         true
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Options
% 3.25/1.02  
% 3.25/1.02  --superposition_flag                    true
% 3.25/1.02  --sup_passive_queue_type                priority_queues
% 3.25/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.02  --demod_completeness_check              fast
% 3.25/1.02  --demod_use_ground                      true
% 3.25/1.02  --sup_to_prop_solver                    passive
% 3.25/1.02  --sup_prop_simpl_new                    true
% 3.25/1.02  --sup_prop_simpl_given                  true
% 3.25/1.02  --sup_fun_splitting                     false
% 3.25/1.02  --sup_smt_interval                      50000
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Simplification Setup
% 3.25/1.02  
% 3.25/1.02  --sup_indices_passive                   []
% 3.25/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_full_bw                           [BwDemod]
% 3.25/1.02  --sup_immed_triv                        [TrivRules]
% 3.25/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_immed_bw_main                     []
% 3.25/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  
% 3.25/1.02  ------ Combination Options
% 3.25/1.02  
% 3.25/1.02  --comb_res_mult                         3
% 3.25/1.02  --comb_sup_mult                         2
% 3.25/1.02  --comb_inst_mult                        10
% 3.25/1.02  
% 3.25/1.02  ------ Debug Options
% 3.25/1.02  
% 3.25/1.02  --dbg_backtrace                         false
% 3.25/1.02  --dbg_dump_prop_clauses                 false
% 3.25/1.02  --dbg_dump_prop_clauses_file            -
% 3.25/1.02  --dbg_out_stat                          false
% 3.25/1.02  ------ Parsing...
% 3.25/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/1.02  ------ Proving...
% 3.25/1.02  ------ Problem Properties 
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  clauses                                 27
% 3.25/1.02  conjectures                             5
% 3.25/1.02  EPR                                     6
% 3.25/1.02  Horn                                    20
% 3.25/1.02  unary                                   9
% 3.25/1.02  binary                                  9
% 3.25/1.02  lits                                    64
% 3.25/1.02  lits eq                                 28
% 3.25/1.02  fd_pure                                 0
% 3.25/1.02  fd_pseudo                               0
% 3.25/1.02  fd_cond                                 1
% 3.25/1.02  fd_pseudo_cond                          3
% 3.25/1.02  AC symbols                              0
% 3.25/1.02  
% 3.25/1.02  ------ Schedule dynamic 5 is on 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  ------ 
% 3.25/1.02  Current options:
% 3.25/1.02  ------ 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options
% 3.25/1.02  
% 3.25/1.02  --out_options                           all
% 3.25/1.02  --tptp_safe_out                         true
% 3.25/1.02  --problem_path                          ""
% 3.25/1.02  --include_path                          ""
% 3.25/1.02  --clausifier                            res/vclausify_rel
% 3.25/1.02  --clausifier_options                    --mode clausify
% 3.25/1.02  --stdin                                 false
% 3.25/1.02  --stats_out                             all
% 3.25/1.02  
% 3.25/1.02  ------ General Options
% 3.25/1.02  
% 3.25/1.02  --fof                                   false
% 3.25/1.02  --time_out_real                         305.
% 3.25/1.02  --time_out_virtual                      -1.
% 3.25/1.02  --symbol_type_check                     false
% 3.25/1.02  --clausify_out                          false
% 3.25/1.02  --sig_cnt_out                           false
% 3.25/1.02  --trig_cnt_out                          false
% 3.25/1.02  --trig_cnt_out_tolerance                1.
% 3.25/1.02  --trig_cnt_out_sk_spl                   false
% 3.25/1.02  --abstr_cl_out                          false
% 3.25/1.02  
% 3.25/1.02  ------ Global Options
% 3.25/1.02  
% 3.25/1.02  --schedule                              default
% 3.25/1.02  --add_important_lit                     false
% 3.25/1.02  --prop_solver_per_cl                    1000
% 3.25/1.02  --min_unsat_core                        false
% 3.25/1.02  --soft_assumptions                      false
% 3.25/1.02  --soft_lemma_size                       3
% 3.25/1.02  --prop_impl_unit_size                   0
% 3.25/1.02  --prop_impl_unit                        []
% 3.25/1.02  --share_sel_clauses                     true
% 3.25/1.02  --reset_solvers                         false
% 3.25/1.02  --bc_imp_inh                            [conj_cone]
% 3.25/1.02  --conj_cone_tolerance                   3.
% 3.25/1.02  --extra_neg_conj                        none
% 3.25/1.02  --large_theory_mode                     true
% 3.25/1.02  --prolific_symb_bound                   200
% 3.25/1.02  --lt_threshold                          2000
% 3.25/1.02  --clause_weak_htbl                      true
% 3.25/1.02  --gc_record_bc_elim                     false
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing Options
% 3.25/1.02  
% 3.25/1.02  --preprocessing_flag                    true
% 3.25/1.02  --time_out_prep_mult                    0.1
% 3.25/1.02  --splitting_mode                        input
% 3.25/1.02  --splitting_grd                         true
% 3.25/1.02  --splitting_cvd                         false
% 3.25/1.02  --splitting_cvd_svl                     false
% 3.25/1.02  --splitting_nvd                         32
% 3.25/1.02  --sub_typing                            true
% 3.25/1.02  --prep_gs_sim                           true
% 3.25/1.02  --prep_unflatten                        true
% 3.25/1.02  --prep_res_sim                          true
% 3.25/1.02  --prep_upred                            true
% 3.25/1.02  --prep_sem_filter                       exhaustive
% 3.25/1.02  --prep_sem_filter_out                   false
% 3.25/1.02  --pred_elim                             true
% 3.25/1.02  --res_sim_input                         true
% 3.25/1.02  --eq_ax_congr_red                       true
% 3.25/1.02  --pure_diseq_elim                       true
% 3.25/1.02  --brand_transform                       false
% 3.25/1.02  --non_eq_to_eq                          false
% 3.25/1.02  --prep_def_merge                        true
% 3.25/1.02  --prep_def_merge_prop_impl              false
% 3.25/1.02  --prep_def_merge_mbd                    true
% 3.25/1.02  --prep_def_merge_tr_red                 false
% 3.25/1.02  --prep_def_merge_tr_cl                  false
% 3.25/1.02  --smt_preprocessing                     true
% 3.25/1.02  --smt_ac_axioms                         fast
% 3.25/1.02  --preprocessed_out                      false
% 3.25/1.02  --preprocessed_stats                    false
% 3.25/1.02  
% 3.25/1.02  ------ Abstraction refinement Options
% 3.25/1.02  
% 3.25/1.02  --abstr_ref                             []
% 3.25/1.02  --abstr_ref_prep                        false
% 3.25/1.02  --abstr_ref_until_sat                   false
% 3.25/1.02  --abstr_ref_sig_restrict                funpre
% 3.25/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.02  --abstr_ref_under                       []
% 3.25/1.02  
% 3.25/1.02  ------ SAT Options
% 3.25/1.02  
% 3.25/1.02  --sat_mode                              false
% 3.25/1.02  --sat_fm_restart_options                ""
% 3.25/1.02  --sat_gr_def                            false
% 3.25/1.02  --sat_epr_types                         true
% 3.25/1.02  --sat_non_cyclic_types                  false
% 3.25/1.02  --sat_finite_models                     false
% 3.25/1.02  --sat_fm_lemmas                         false
% 3.25/1.02  --sat_fm_prep                           false
% 3.25/1.02  --sat_fm_uc_incr                        true
% 3.25/1.02  --sat_out_model                         small
% 3.25/1.02  --sat_out_clauses                       false
% 3.25/1.02  
% 3.25/1.02  ------ QBF Options
% 3.25/1.02  
% 3.25/1.02  --qbf_mode                              false
% 3.25/1.02  --qbf_elim_univ                         false
% 3.25/1.02  --qbf_dom_inst                          none
% 3.25/1.02  --qbf_dom_pre_inst                      false
% 3.25/1.02  --qbf_sk_in                             false
% 3.25/1.02  --qbf_pred_elim                         true
% 3.25/1.02  --qbf_split                             512
% 3.25/1.02  
% 3.25/1.02  ------ BMC1 Options
% 3.25/1.02  
% 3.25/1.02  --bmc1_incremental                      false
% 3.25/1.02  --bmc1_axioms                           reachable_all
% 3.25/1.02  --bmc1_min_bound                        0
% 3.25/1.02  --bmc1_max_bound                        -1
% 3.25/1.02  --bmc1_max_bound_default                -1
% 3.25/1.02  --bmc1_symbol_reachability              true
% 3.25/1.02  --bmc1_property_lemmas                  false
% 3.25/1.02  --bmc1_k_induction                      false
% 3.25/1.02  --bmc1_non_equiv_states                 false
% 3.25/1.02  --bmc1_deadlock                         false
% 3.25/1.02  --bmc1_ucm                              false
% 3.25/1.02  --bmc1_add_unsat_core                   none
% 3.25/1.02  --bmc1_unsat_core_children              false
% 3.25/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.02  --bmc1_out_stat                         full
% 3.25/1.02  --bmc1_ground_init                      false
% 3.25/1.02  --bmc1_pre_inst_next_state              false
% 3.25/1.02  --bmc1_pre_inst_state                   false
% 3.25/1.02  --bmc1_pre_inst_reach_state             false
% 3.25/1.02  --bmc1_out_unsat_core                   false
% 3.25/1.02  --bmc1_aig_witness_out                  false
% 3.25/1.02  --bmc1_verbose                          false
% 3.25/1.02  --bmc1_dump_clauses_tptp                false
% 3.25/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.02  --bmc1_dump_file                        -
% 3.25/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.02  --bmc1_ucm_extend_mode                  1
% 3.25/1.02  --bmc1_ucm_init_mode                    2
% 3.25/1.02  --bmc1_ucm_cone_mode                    none
% 3.25/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.02  --bmc1_ucm_relax_model                  4
% 3.25/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.02  --bmc1_ucm_layered_model                none
% 3.25/1.02  --bmc1_ucm_max_lemma_size               10
% 3.25/1.02  
% 3.25/1.02  ------ AIG Options
% 3.25/1.02  
% 3.25/1.02  --aig_mode                              false
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation Options
% 3.25/1.02  
% 3.25/1.02  --instantiation_flag                    true
% 3.25/1.02  --inst_sos_flag                         false
% 3.25/1.02  --inst_sos_phase                        true
% 3.25/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel_side                     none
% 3.25/1.02  --inst_solver_per_active                1400
% 3.25/1.02  --inst_solver_calls_frac                1.
% 3.25/1.02  --inst_passive_queue_type               priority_queues
% 3.25/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.02  --inst_passive_queues_freq              [25;2]
% 3.25/1.02  --inst_dismatching                      true
% 3.25/1.02  --inst_eager_unprocessed_to_passive     true
% 3.25/1.02  --inst_prop_sim_given                   true
% 3.25/1.02  --inst_prop_sim_new                     false
% 3.25/1.02  --inst_subs_new                         false
% 3.25/1.02  --inst_eq_res_simp                      false
% 3.25/1.02  --inst_subs_given                       false
% 3.25/1.02  --inst_orphan_elimination               true
% 3.25/1.02  --inst_learning_loop_flag               true
% 3.25/1.02  --inst_learning_start                   3000
% 3.25/1.02  --inst_learning_factor                  2
% 3.25/1.02  --inst_start_prop_sim_after_learn       3
% 3.25/1.02  --inst_sel_renew                        solver
% 3.25/1.02  --inst_lit_activity_flag                true
% 3.25/1.02  --inst_restr_to_given                   false
% 3.25/1.02  --inst_activity_threshold               500
% 3.25/1.02  --inst_out_proof                        true
% 3.25/1.02  
% 3.25/1.02  ------ Resolution Options
% 3.25/1.02  
% 3.25/1.02  --resolution_flag                       false
% 3.25/1.02  --res_lit_sel                           adaptive
% 3.25/1.02  --res_lit_sel_side                      none
% 3.25/1.02  --res_ordering                          kbo
% 3.25/1.02  --res_to_prop_solver                    active
% 3.25/1.02  --res_prop_simpl_new                    false
% 3.25/1.02  --res_prop_simpl_given                  true
% 3.25/1.02  --res_passive_queue_type                priority_queues
% 3.25/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.02  --res_passive_queues_freq               [15;5]
% 3.25/1.02  --res_forward_subs                      full
% 3.25/1.02  --res_backward_subs                     full
% 3.25/1.02  --res_forward_subs_resolution           true
% 3.25/1.02  --res_backward_subs_resolution          true
% 3.25/1.02  --res_orphan_elimination                true
% 3.25/1.02  --res_time_limit                        2.
% 3.25/1.02  --res_out_proof                         true
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Options
% 3.25/1.02  
% 3.25/1.02  --superposition_flag                    true
% 3.25/1.02  --sup_passive_queue_type                priority_queues
% 3.25/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.02  --demod_completeness_check              fast
% 3.25/1.02  --demod_use_ground                      true
% 3.25/1.02  --sup_to_prop_solver                    passive
% 3.25/1.02  --sup_prop_simpl_new                    true
% 3.25/1.02  --sup_prop_simpl_given                  true
% 3.25/1.02  --sup_fun_splitting                     false
% 3.25/1.02  --sup_smt_interval                      50000
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Simplification Setup
% 3.25/1.02  
% 3.25/1.02  --sup_indices_passive                   []
% 3.25/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_full_bw                           [BwDemod]
% 3.25/1.02  --sup_immed_triv                        [TrivRules]
% 3.25/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_immed_bw_main                     []
% 3.25/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  
% 3.25/1.02  ------ Combination Options
% 3.25/1.02  
% 3.25/1.02  --comb_res_mult                         3
% 3.25/1.02  --comb_sup_mult                         2
% 3.25/1.02  --comb_inst_mult                        10
% 3.25/1.02  
% 3.25/1.02  ------ Debug Options
% 3.25/1.02  
% 3.25/1.02  --dbg_backtrace                         false
% 3.25/1.02  --dbg_dump_prop_clauses                 false
% 3.25/1.02  --dbg_dump_prop_clauses_file            -
% 3.25/1.02  --dbg_out_stat                          false
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  ------ Proving...
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  % SZS status Theorem for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  fof(f13,conjecture,(
% 3.25/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f14,negated_conjecture,(
% 3.25/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.25/1.02    inference(negated_conjecture,[],[f13])).
% 3.25/1.02  
% 3.25/1.02  fof(f27,plain,(
% 3.25/1.02    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.25/1.02    inference(ennf_transformation,[],[f14])).
% 3.25/1.02  
% 3.25/1.02  fof(f28,plain,(
% 3.25/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.25/1.02    inference(flattening,[],[f27])).
% 3.25/1.02  
% 3.25/1.02  fof(f44,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f43,plain,(
% 3.25/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f45,plain,(
% 3.25/1.02    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f28,f44,f43])).
% 3.25/1.02  
% 3.25/1.02  fof(f77,plain,(
% 3.25/1.02    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f1,axiom,(
% 3.25/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f16,plain,(
% 3.25/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f1])).
% 3.25/1.02  
% 3.25/1.02  fof(f29,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(nnf_transformation,[],[f16])).
% 3.25/1.02  
% 3.25/1.02  fof(f30,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(rectify,[],[f29])).
% 3.25/1.02  
% 3.25/1.02  fof(f31,plain,(
% 3.25/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f32,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.25/1.02  
% 3.25/1.02  fof(f46,plain,(
% 3.25/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f32])).
% 3.25/1.02  
% 3.25/1.02  fof(f12,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f25,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f12])).
% 3.25/1.02  
% 3.25/1.02  fof(f26,plain,(
% 3.25/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(flattening,[],[f25])).
% 3.25/1.02  
% 3.25/1.02  fof(f42,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(nnf_transformation,[],[f26])).
% 3.25/1.02  
% 3.25/1.02  fof(f65,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f42])).
% 3.25/1.02  
% 3.25/1.02  fof(f75,plain,(
% 3.25/1.02    v1_funct_2(sK6,sK3,sK4)),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f76,plain,(
% 3.25/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f10,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f22,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f10])).
% 3.25/1.02  
% 3.25/1.02  fof(f63,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f22])).
% 3.25/1.02  
% 3.25/1.02  fof(f72,plain,(
% 3.25/1.02    v1_funct_2(sK5,sK3,sK4)),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f73,plain,(
% 3.25/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f7,axiom,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f18,plain,(
% 3.25/1.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f7])).
% 3.25/1.02  
% 3.25/1.02  fof(f19,plain,(
% 3.25/1.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(flattening,[],[f18])).
% 3.25/1.02  
% 3.25/1.02  fof(f40,plain,(
% 3.25/1.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f41,plain,(
% 3.25/1.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f40])).
% 3.25/1.02  
% 3.25/1.02  fof(f59,plain,(
% 3.25/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f41])).
% 3.25/1.02  
% 3.25/1.02  fof(f71,plain,(
% 3.25/1.02    v1_funct_1(sK5)),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f8,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f20,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f8])).
% 3.25/1.02  
% 3.25/1.02  fof(f61,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f20])).
% 3.25/1.02  
% 3.25/1.02  fof(f74,plain,(
% 3.25/1.02    v1_funct_1(sK6)),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f5,axiom,(
% 3.25/1.02    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f37,plain,(
% 3.25/1.02    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK1(X0),X0))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f38,plain,(
% 3.25/1.02    ! [X0] : m1_subset_1(sK1(X0),X0)),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f37])).
% 3.25/1.02  
% 3.25/1.02  fof(f56,plain,(
% 3.25/1.02    ( ! [X0] : (m1_subset_1(sK1(X0),X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f38])).
% 3.25/1.02  
% 3.25/1.02  fof(f11,axiom,(
% 3.25/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f23,plain,(
% 3.25/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/1.02    inference(ennf_transformation,[],[f11])).
% 3.25/1.02  
% 3.25/1.02  fof(f24,plain,(
% 3.25/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(flattening,[],[f23])).
% 3.25/1.02  
% 3.25/1.02  fof(f64,plain,(
% 3.25/1.02    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f24])).
% 3.25/1.02  
% 3.25/1.02  fof(f78,plain,(
% 3.25/1.02    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.25/1.02    inference(cnf_transformation,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f60,plain,(
% 3.25/1.02    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f41])).
% 3.25/1.02  
% 3.25/1.02  fof(f4,axiom,(
% 3.25/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f35,plain,(
% 3.25/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/1.02    inference(nnf_transformation,[],[f4])).
% 3.25/1.02  
% 3.25/1.02  fof(f36,plain,(
% 3.25/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/1.02    inference(flattening,[],[f35])).
% 3.25/1.02  
% 3.25/1.02  fof(f55,plain,(
% 3.25/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.25/1.02    inference(cnf_transformation,[],[f36])).
% 3.25/1.02  
% 3.25/1.02  fof(f81,plain,(
% 3.25/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.25/1.02    inference(equality_resolution,[],[f55])).
% 3.25/1.02  
% 3.25/1.02  fof(f54,plain,(
% 3.25/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.25/1.02    inference(cnf_transformation,[],[f36])).
% 3.25/1.02  
% 3.25/1.02  fof(f82,plain,(
% 3.25/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.25/1.02    inference(equality_resolution,[],[f54])).
% 3.25/1.02  
% 3.25/1.02  fof(f66,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f42])).
% 3.25/1.02  
% 3.25/1.02  fof(f87,plain,(
% 3.25/1.02    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.25/1.02    inference(equality_resolution,[],[f66])).
% 3.25/1.02  
% 3.25/1.02  fof(f69,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f42])).
% 3.25/1.02  
% 3.25/1.02  fof(f85,plain,(
% 3.25/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.25/1.02    inference(equality_resolution,[],[f69])).
% 3.25/1.02  
% 3.25/1.02  fof(f3,axiom,(
% 3.25/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f52,plain,(
% 3.25/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f3])).
% 3.25/1.02  
% 3.25/1.02  fof(f2,axiom,(
% 3.25/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f33,plain,(
% 3.25/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.25/1.02    inference(nnf_transformation,[],[f2])).
% 3.25/1.02  
% 3.25/1.02  fof(f34,plain,(
% 3.25/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.25/1.02    inference(flattening,[],[f33])).
% 3.25/1.02  
% 3.25/1.02  fof(f51,plain,(
% 3.25/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f34])).
% 3.25/1.02  
% 3.25/1.02  fof(f9,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f15,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.25/1.02    inference(pure_predicate_removal,[],[f9])).
% 3.25/1.02  
% 3.25/1.02  fof(f21,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f15])).
% 3.25/1.02  
% 3.25/1.02  fof(f62,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f21])).
% 3.25/1.02  
% 3.25/1.02  fof(f6,axiom,(
% 3.25/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.25/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f17,plain,(
% 3.25/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.25/1.02    inference(ennf_transformation,[],[f6])).
% 3.25/1.02  
% 3.25/1.02  fof(f39,plain,(
% 3.25/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.25/1.02    inference(nnf_transformation,[],[f17])).
% 3.25/1.02  
% 3.25/1.02  fof(f57,plain,(
% 3.25/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f39])).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1586,plain,( X0 = X0 ),theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_6045,plain,
% 3.25/1.02      ( k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6)) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1587,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5596,plain,
% 3.25/1.02      ( k1_funct_1(sK6,sK2(sK5,sK6)) != X0
% 3.25/1.02      | k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK5,sK2(sK5,sK6))
% 3.25/1.02      | k1_funct_1(sK5,sK2(sK5,sK6)) != X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_6044,plain,
% 3.25/1.02      ( k1_funct_1(sK6,sK2(sK5,sK6)) != k1_funct_1(sK6,sK2(sK5,sK6))
% 3.25/1.02      | k1_funct_1(sK6,sK2(sK5,sK6)) = k1_funct_1(sK5,sK2(sK5,sK6))
% 3.25/1.02      | k1_funct_1(sK5,sK2(sK5,sK6)) != k1_funct_1(sK6,sK2(sK5,sK6)) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_5596]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_26,negated_conjecture,
% 3.25/1.02      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5608,plain,
% 3.25/1.02      ( ~ r2_hidden(sK2(sK5,sK6),sK3)
% 3.25/1.02      | k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6)) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_26]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2,plain,
% 3.25/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.25/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2654,plain,
% 3.25/1.02      ( r2_hidden(sK2(sK5,sK6),X0)
% 3.25/1.02      | ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
% 3.25/1.02      | ~ r1_tarski(k1_relat_1(sK5),X0) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5607,plain,
% 3.25/1.02      ( ~ r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
% 3.25/1.02      | r2_hidden(sK2(sK5,sK6),sK3)
% 3.25/1.02      | ~ r1_tarski(k1_relat_1(sK5),sK3) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2654]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_24,plain,
% 3.25/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.02      | k1_xboole_0 = X2 ),
% 3.25/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_28,negated_conjecture,
% 3.25/1.02      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.25/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_903,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.02      | sK6 != X0
% 3.25/1.02      | sK4 != X2
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | k1_xboole_0 = X2 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_904,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.25/1.02      | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_903]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_27,negated_conjecture,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_906,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_904,c_27]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1989,plain,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_17,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1991,plain,
% 3.25/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2882,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1989,c_1991]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3214,plain,
% 3.25/1.02      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_906,c_2882]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_31,negated_conjecture,
% 3.25/1.02      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.25/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_914,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.02      | sK5 != X0
% 3.25/1.02      | sK4 != X2
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | k1_xboole_0 = X2 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_915,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.25/1.02      | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_914]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_30,negated_conjecture,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_917,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_915,c_30]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1987,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2883,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1987,c_1991]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3303,plain,
% 3.25/1.02      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_917,c_2883]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_14,plain,
% 3.25/1.02      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.25/1.02      | ~ v1_funct_1(X1)
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X1)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | X1 = X0
% 3.25/1.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.25/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1993,plain,
% 3.25/1.02      ( X0 = X1
% 3.25/1.02      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.25/1.02      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top
% 3.25/1.02      | v1_funct_1(X1) != iProver_top
% 3.25/1.02      | v1_relat_1(X1) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3482,plain,
% 3.25/1.02      ( k1_relat_1(X0) != sK3
% 3.25/1.02      | sK5 = X0
% 3.25/1.02      | sK4 = k1_xboole_0
% 3.25/1.02      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top
% 3.25/1.02      | v1_funct_1(sK5) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3303,c_1993]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_32,negated_conjecture,
% 3.25/1.02      ( v1_funct_1(sK5) ),
% 3.25/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_33,plain,
% 3.25/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_35,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_15,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2197,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | v1_relat_1(sK5) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2198,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2197]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3848,plain,
% 3.25/1.02      ( v1_relat_1(X0) != iProver_top
% 3.25/1.02      | k1_relat_1(X0) != sK3
% 3.25/1.02      | sK5 = X0
% 3.25/1.02      | sK4 = k1_xboole_0
% 3.25/1.02      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_3482,c_33,c_35,c_2198]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3849,plain,
% 3.25/1.02      ( k1_relat_1(X0) != sK3
% 3.25/1.02      | sK5 = X0
% 3.25/1.02      | sK4 = k1_xboole_0
% 3.25/1.02      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_3848]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3860,plain,
% 3.25/1.02      ( sK6 = sK5
% 3.25/1.02      | sK4 = k1_xboole_0
% 3.25/1.02      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 3.25/1.02      | v1_funct_1(sK6) != iProver_top
% 3.25/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3214,c_3849]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_29,negated_conjecture,
% 3.25/1.02      ( v1_funct_1(sK6) ),
% 3.25/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_36,plain,
% 3.25/1.02      ( v1_funct_1(sK6) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_38,plain,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_10,plain,
% 3.25/1.02      ( m1_subset_1(sK1(X0),X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_18,plain,
% 3.25/1.02      ( r2_relset_1(X0,X1,X2,X2)
% 3.25/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.25/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_25,negated_conjecture,
% 3.25/1.02      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.25/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_326,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | sK6 != X3
% 3.25/1.02      | sK5 != X3
% 3.25/1.02      | sK4 != X2
% 3.25/1.02      | sK3 != X1 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_327,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | sK5 != sK6 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_326]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_331,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | sK5 != sK6 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_327,c_27]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_476,plain,
% 3.25/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != X0
% 3.25/1.02      | sK1(X0) != X1
% 3.25/1.02      | sK6 != sK5 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_331]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_477,plain,
% 3.25/1.02      ( sK6 != sK5 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_476]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2194,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | v1_relat_1(sK6) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2195,plain,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.25/1.02      | v1_relat_1(sK6) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3886,plain,
% 3.25/1.02      ( sK4 = k1_xboole_0
% 3.25/1.02      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_3860,c_36,c_38,c_477,c_2195]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3892,plain,
% 3.25/1.02      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3303,c_3886]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1990,plain,
% 3.25/1.02      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 3.25/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3897,plain,
% 3.25/1.02      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 3.25/1.02      | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3892,c_1990]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_13,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(X1)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X1)
% 3.25/1.02      | X0 = X1
% 3.25/1.02      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.25/1.02      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1994,plain,
% 3.25/1.02      ( X0 = X1
% 3.25/1.02      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.25/1.02      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.25/1.02      | v1_funct_1(X1) != iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) != iProver_top
% 3.25/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3962,plain,
% 3.25/1.02      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.25/1.02      | sK6 = sK5
% 3.25/1.02      | sK4 = k1_xboole_0
% 3.25/1.02      | v1_funct_1(sK6) != iProver_top
% 3.25/1.02      | v1_funct_1(sK5) != iProver_top
% 3.25/1.02      | v1_relat_1(sK6) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3897,c_1994]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3979,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK6)
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK6)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.25/1.02      | sK6 = sK5
% 3.25/1.02      | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_3962]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4448,plain,
% 3.25/1.02      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_3962,c_32,c_30,c_29,c_27,c_477,c_2194,c_2197,c_3979]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4452,plain,
% 3.25/1.02      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3214,c_4448]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4494,plain,
% 3.25/1.02      ( sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4452,c_3303]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4510,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4494,c_1987]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_7,plain,
% 3.25/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4512,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4510,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_8,plain,
% 3.25/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2885,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.25/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_8,c_1991]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4559,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4512,c_2885]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_23,plain,
% 3.25/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_890,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.25/1.02      | sK5 != X0
% 3.25/1.02      | sK4 != X1
% 3.25/1.02      | sK3 != k1_xboole_0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_891,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.25/1.02      | sK3 != k1_xboole_0 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_890]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1980,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.25/1.02      | sK3 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2074,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.25/1.02      | sK3 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1980,c_8]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4505,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.25/1.02      | sK3 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4494,c_2074]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4525,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.25/1.02      | sK3 != k1_xboole_0 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4505,c_4512]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_20,plain,
% 3.25/1.02      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | k1_xboole_0 = X1
% 3.25/1.02      | k1_xboole_0 = X0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_857,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | sK5 != X0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | k1_xboole_0 = X1
% 3.25/1.02      | k1_xboole_0 = X0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_858,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK5
% 3.25/1.02      | k1_xboole_0 = sK3 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_857]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1982,plain,
% 3.25/1.02      ( sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK5
% 3.25/1.02      | k1_xboole_0 = sK3
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2088,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1982,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4503,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | k1_xboole_0 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4494,c_2088]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4534,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(equality_resolution_simp,[status(thm)],[c_4503]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4538,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4534,c_4512]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1588,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.25/1.02      theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2369,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,sK5) | r1_tarski(sK6,sK5) | sK6 != X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2371,plain,
% 3.25/1.02      ( r1_tarski(sK6,sK5)
% 3.25/1.02      | ~ r1_tarski(k1_xboole_0,sK5)
% 3.25/1.02      | sK6 != k1_xboole_0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2369]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_6,plain,
% 3.25/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2559,plain,
% 3.25/1.02      ( r1_tarski(k1_xboole_0,sK6) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2579,plain,
% 3.25/1.02      ( r1_tarski(k1_xboole_0,sK5) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2461,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3083,plain,
% 3.25/1.02      ( ~ r1_tarski(sK6,sK5) | ~ r1_tarski(sK5,sK6) | sK6 = sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2461]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2564,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,sK6) | r1_tarski(X1,sK6) | X1 != X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3281,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,sK6) | r1_tarski(sK5,sK6) | sK5 != X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2564]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3283,plain,
% 3.25/1.02      ( r1_tarski(sK5,sK6)
% 3.25/1.02      | ~ r1_tarski(k1_xboole_0,sK6)
% 3.25/1.02      | sK5 != k1_xboole_0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_3281]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_841,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | sK6 != X0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | k1_xboole_0 = X1
% 3.25/1.02      | k1_xboole_0 = X0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_842,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK6
% 3.25/1.02      | k1_xboole_0 = sK3 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_841]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1983,plain,
% 3.25/1.02      ( sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK6
% 3.25/1.02      | k1_xboole_0 = sK3
% 3.25/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2097,plain,
% 3.25/1.02      ( sK6 = k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1983,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4502,plain,
% 3.25/1.02      ( sK6 = k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | k1_xboole_0 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4494,c_2097]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4541,plain,
% 3.25/1.02      ( sK6 = k1_xboole_0
% 3.25/1.02      | sK3 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(equality_resolution_simp,[status(thm)],[c_4502]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4509,plain,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4494,c_1989]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4515,plain,
% 3.25/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4509,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4545,plain,
% 3.25/1.02      ( sK6 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4541,c_4515]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5336,plain,
% 3.25/1.02      ( sK3 = k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4538,c_477,c_2371,c_2559,c_2579,c_3083,c_3283,c_4545]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5532,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4525,c_477,c_2371,c_2559,c_2579,c_3083,c_3283,c_4538,
% 3.25/1.02                 c_4545]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5535,plain,
% 3.25/1.02      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4559,c_5532]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_16,plain,
% 3.25/1.02      ( v4_relat_1(X0,X1)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_12,plain,
% 3.25/1.02      ( ~ v4_relat_1(X0,X1)
% 3.25/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 3.25/1.02      | ~ v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_347,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 3.25/1.02      | ~ v1_relat_1(X0) ),
% 3.25/1.02      inference(resolution,[status(thm)],[c_16,c_12]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_351,plain,
% 3.25/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_347,c_15]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_352,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_351]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1984,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2397,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_7,c_1984]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4711,plain,
% 3.25/1.02      ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4515,c_2397]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4722,plain,
% 3.25/1.02      ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_4711]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4297,plain,
% 3.25/1.02      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4300,plain,
% 3.25/1.02      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_4297]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2794,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,k1_relat_1(sK6))
% 3.25/1.02      | ~ r1_tarski(k1_relat_1(sK6),X0)
% 3.25/1.02      | k1_relat_1(sK6) = X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2795,plain,
% 3.25/1.02      ( k1_relat_1(sK6) = X0
% 3.25/1.02      | r1_tarski(X0,k1_relat_1(sK6)) != iProver_top
% 3.25/1.02      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2797,plain,
% 3.25/1.02      ( k1_relat_1(sK6) = k1_xboole_0
% 3.25/1.02      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.25/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2795]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2672,plain,
% 3.25/1.02      ( k1_relat_1(sK6) != X0
% 3.25/1.02      | k1_relat_1(sK5) != X0
% 3.25/1.02      | k1_relat_1(sK5) = k1_relat_1(sK6) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2673,plain,
% 3.25/1.02      ( k1_relat_1(sK6) != k1_xboole_0
% 3.25/1.02      | k1_relat_1(sK5) = k1_relat_1(sK6)
% 3.25/1.02      | k1_relat_1(sK5) != k1_xboole_0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2672]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2308,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | X0 = sK5
% 3.25/1.02      | k1_funct_1(X0,sK2(sK5,X0)) != k1_funct_1(sK5,sK2(sK5,X0))
% 3.25/1.02      | k1_relat_1(sK5) != k1_relat_1(X0) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2622,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK6)
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK6)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k1_funct_1(sK6,sK2(sK5,sK6)) != k1_funct_1(sK5,sK2(sK5,sK6))
% 3.25/1.02      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.25/1.02      | sK6 = sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2308]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2313,plain,
% 3.25/1.02      ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | X0 = sK5
% 3.25/1.02      | k1_relat_1(sK5) != k1_relat_1(X0) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2616,plain,
% 3.25/1.02      ( r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5))
% 3.25/1.02      | ~ v1_funct_1(sK6)
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK6)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.25/1.02      | sK6 = sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2313]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2219,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | r1_tarski(k1_relat_1(sK5),sK3) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_352]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(contradiction,plain,
% 3.25/1.02      ( $false ),
% 3.25/1.02      inference(minisat,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_6045,c_6044,c_5608,c_5607,c_5535,c_4722,c_4300,c_2797,
% 3.25/1.02                 c_2673,c_2622,c_2616,c_2219,c_2197,c_2194,c_477,c_27,
% 3.25/1.02                 c_29,c_30,c_32]) ).
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  ------                               Statistics
% 3.25/1.02  
% 3.25/1.02  ------ General
% 3.25/1.02  
% 3.25/1.02  abstr_ref_over_cycles:                  0
% 3.25/1.02  abstr_ref_under_cycles:                 0
% 3.25/1.02  gc_basic_clause_elim:                   0
% 3.25/1.02  forced_gc_time:                         0
% 3.25/1.02  parsing_time:                           0.009
% 3.25/1.02  unif_index_cands_time:                  0.
% 3.25/1.02  unif_index_add_time:                    0.
% 3.25/1.02  orderings_time:                         0.
% 3.25/1.02  out_proof_time:                         0.02
% 3.25/1.02  total_time:                             0.263
% 3.25/1.02  num_of_symbols:                         52
% 3.25/1.02  num_of_terms:                           5126
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing
% 3.25/1.02  
% 3.25/1.02  num_of_splits:                          0
% 3.25/1.02  num_of_split_atoms:                     0
% 3.25/1.02  num_of_reused_defs:                     0
% 3.25/1.02  num_eq_ax_congr_red:                    28
% 3.25/1.02  num_of_sem_filtered_clauses:            1
% 3.25/1.02  num_of_subtypes:                        0
% 3.25/1.02  monotx_restored_types:                  0
% 3.25/1.02  sat_num_of_epr_types:                   0
% 3.25/1.02  sat_num_of_non_cyclic_types:            0
% 3.25/1.02  sat_guarded_non_collapsed_types:        0
% 3.25/1.02  num_pure_diseq_elim:                    0
% 3.25/1.02  simp_replaced_by:                       0
% 3.25/1.02  res_preprocessed:                       134
% 3.25/1.02  prep_upred:                             0
% 3.25/1.02  prep_unflattend:                        114
% 3.25/1.02  smt_new_axioms:                         0
% 3.25/1.02  pred_elim_cands:                        5
% 3.25/1.02  pred_elim:                              3
% 3.25/1.02  pred_elim_cl:                           5
% 3.25/1.02  pred_elim_cycles:                       6
% 3.25/1.02  merged_defs:                            0
% 3.25/1.02  merged_defs_ncl:                        0
% 3.25/1.02  bin_hyper_res:                          0
% 3.25/1.02  prep_cycles:                            4
% 3.25/1.02  pred_elim_time:                         0.023
% 3.25/1.02  splitting_time:                         0.
% 3.25/1.02  sem_filter_time:                        0.
% 3.25/1.02  monotx_time:                            0.001
% 3.25/1.02  subtype_inf_time:                       0.
% 3.25/1.02  
% 3.25/1.02  ------ Problem properties
% 3.25/1.02  
% 3.25/1.02  clauses:                                27
% 3.25/1.02  conjectures:                            5
% 3.25/1.02  epr:                                    6
% 3.25/1.02  horn:                                   20
% 3.25/1.02  ground:                                 10
% 3.25/1.02  unary:                                  9
% 3.25/1.02  binary:                                 9
% 3.25/1.02  lits:                                   64
% 3.25/1.02  lits_eq:                                28
% 3.25/1.02  fd_pure:                                0
% 3.25/1.02  fd_pseudo:                              0
% 3.25/1.02  fd_cond:                                1
% 3.25/1.02  fd_pseudo_cond:                         3
% 3.25/1.02  ac_symbols:                             0
% 3.25/1.02  
% 3.25/1.02  ------ Propositional Solver
% 3.25/1.02  
% 3.25/1.02  prop_solver_calls:                      30
% 3.25/1.02  prop_fast_solver_calls:                 1100
% 3.25/1.02  smt_solver_calls:                       0
% 3.25/1.02  smt_fast_solver_calls:                  0
% 3.25/1.02  prop_num_of_clauses:                    1951
% 3.25/1.02  prop_preprocess_simplified:             5842
% 3.25/1.02  prop_fo_subsumed:                       43
% 3.25/1.02  prop_solver_time:                       0.
% 3.25/1.02  smt_solver_time:                        0.
% 3.25/1.02  smt_fast_solver_time:                   0.
% 3.25/1.02  prop_fast_solver_time:                  0.
% 3.25/1.02  prop_unsat_core_time:                   0.
% 3.25/1.02  
% 3.25/1.02  ------ QBF
% 3.25/1.02  
% 3.25/1.02  qbf_q_res:                              0
% 3.25/1.02  qbf_num_tautologies:                    0
% 3.25/1.02  qbf_prep_cycles:                        0
% 3.25/1.02  
% 3.25/1.02  ------ BMC1
% 3.25/1.02  
% 3.25/1.02  bmc1_current_bound:                     -1
% 3.25/1.02  bmc1_last_solved_bound:                 -1
% 3.25/1.02  bmc1_unsat_core_size:                   -1
% 3.25/1.02  bmc1_unsat_core_parents_size:           -1
% 3.25/1.02  bmc1_merge_next_fun:                    0
% 3.25/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation
% 3.25/1.02  
% 3.25/1.02  inst_num_of_clauses:                    658
% 3.25/1.02  inst_num_in_passive:                    294
% 3.25/1.02  inst_num_in_active:                     344
% 3.25/1.02  inst_num_in_unprocessed:                19
% 3.25/1.02  inst_num_of_loops:                      416
% 3.25/1.02  inst_num_of_learning_restarts:          0
% 3.25/1.02  inst_num_moves_active_passive:          67
% 3.25/1.02  inst_lit_activity:                      0
% 3.25/1.02  inst_lit_activity_moves:                0
% 3.25/1.02  inst_num_tautologies:                   0
% 3.25/1.02  inst_num_prop_implied:                  0
% 3.25/1.02  inst_num_existing_simplified:           0
% 3.25/1.02  inst_num_eq_res_simplified:             0
% 3.25/1.02  inst_num_child_elim:                    0
% 3.25/1.02  inst_num_of_dismatching_blockings:      176
% 3.25/1.02  inst_num_of_non_proper_insts:           616
% 3.25/1.02  inst_num_of_duplicates:                 0
% 3.25/1.02  inst_inst_num_from_inst_to_res:         0
% 3.25/1.02  inst_dismatching_checking_time:         0.
% 3.25/1.02  
% 3.25/1.02  ------ Resolution
% 3.25/1.02  
% 3.25/1.02  res_num_of_clauses:                     0
% 3.25/1.02  res_num_in_passive:                     0
% 3.25/1.02  res_num_in_active:                      0
% 3.25/1.02  res_num_of_loops:                       138
% 3.25/1.02  res_forward_subset_subsumed:            78
% 3.25/1.02  res_backward_subset_subsumed:           0
% 3.25/1.02  res_forward_subsumed:                   0
% 3.25/1.02  res_backward_subsumed:                  0
% 3.25/1.02  res_forward_subsumption_resolution:     0
% 3.25/1.02  res_backward_subsumption_resolution:    0
% 3.25/1.02  res_clause_to_clause_subsumption:       204
% 3.25/1.02  res_orphan_elimination:                 0
% 3.25/1.02  res_tautology_del:                      44
% 3.25/1.02  res_num_eq_res_simplified:              0
% 3.25/1.02  res_num_sel_changes:                    0
% 3.25/1.02  res_moves_from_active_to_pass:          0
% 3.25/1.02  
% 3.25/1.02  ------ Superposition
% 3.25/1.02  
% 3.25/1.02  sup_time_total:                         0.
% 3.25/1.02  sup_time_generating:                    0.
% 3.25/1.02  sup_time_sim_full:                      0.
% 3.25/1.02  sup_time_sim_immed:                     0.
% 3.25/1.02  
% 3.25/1.02  sup_num_of_clauses:                     63
% 3.25/1.02  sup_num_in_active:                      47
% 3.25/1.02  sup_num_in_passive:                     16
% 3.25/1.02  sup_num_of_loops:                       82
% 3.25/1.02  sup_fw_superposition:                   87
% 3.25/1.02  sup_bw_superposition:                   32
% 3.25/1.02  sup_immediate_simplified:               25
% 3.25/1.02  sup_given_eliminated:                   0
% 3.25/1.02  comparisons_done:                       0
% 3.25/1.02  comparisons_avoided:                    20
% 3.25/1.02  
% 3.25/1.02  ------ Simplifications
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  sim_fw_subset_subsumed:                 9
% 3.25/1.02  sim_bw_subset_subsumed:                 11
% 3.25/1.02  sim_fw_subsumed:                        6
% 3.25/1.02  sim_bw_subsumed:                        0
% 3.25/1.02  sim_fw_subsumption_res:                 4
% 3.25/1.02  sim_bw_subsumption_res:                 0
% 3.25/1.02  sim_tautology_del:                      0
% 3.25/1.02  sim_eq_tautology_del:                   18
% 3.25/1.02  sim_eq_res_simp:                        2
% 3.25/1.02  sim_fw_demodulated:                     7
% 3.25/1.02  sim_bw_demodulated:                     31
% 3.25/1.02  sim_light_normalised:                   5
% 3.25/1.02  sim_joinable_taut:                      0
% 3.25/1.02  sim_joinable_simp:                      0
% 3.25/1.02  sim_ac_normalised:                      0
% 3.25/1.02  sim_smt_subsumption:                    0
% 3.25/1.02  
%------------------------------------------------------------------------------
