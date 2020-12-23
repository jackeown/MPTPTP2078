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
% DateTime   : Thu Dec  3 12:07:44 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  179 (2361 expanded)
%              Number of clauses        :  118 ( 721 expanded)
%              Number of leaves         :   18 ( 577 expanded)
%              Depth                    :   30
%              Number of atoms          :  658 (15892 expanded)
%              Number of equality atoms :  295 (3387 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f64,plain,(
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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f41,f40])).

fof(f74,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
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

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    v1_funct_1(sK6) ),
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
            | ~ r2_hidden(k4_tarski(X4,X5),X2) )
          & ( r2_hidden(k4_tarski(X4,X5),X3)
            | r2_hidden(k4_tarski(X4,X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK2(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK1(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK2(X0,X1,X2,X3),X1)
                & m1_subset_1(sK1(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | m1_subset_1(sK1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1445,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2151,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(sK3,sK4,sK5,sK6)
    | sK6 != X3
    | sK5 != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_19605,plain,
    ( ~ r2_relset_1(sK3,X0,X1,X2)
    | r2_relset_1(sK3,sK4,sK5,sK6)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_19607,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK6)
    | ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK6 != k1_xboole_0
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_19605])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_501,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_503,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_29])).

cnf(c_2078,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2081,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2569,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2078,c_2081])).

cnf(c_2763,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_503,c_2569])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_514,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_32])).

cnf(c_2076,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2570,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2076,c_2081])).

cnf(c_2826,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_514,c_2570])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2089,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4992,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2089])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2504,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2879,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_2880,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2879])).

cnf(c_7972,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4992,c_38,c_40,c_2880])).

cnf(c_7973,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7972])).

cnf(c_7979,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_7973])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2088,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3785,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_2088])).

cnf(c_8045,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7979,c_35,c_3785])).

cnf(c_8049,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_8045])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2094,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8054,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | m1_subset_1(sK0(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8049,c_2094])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2079,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12516,plain,
    ( k1_funct_1(sK5,sK0(sK5,sK6)) = k1_funct_1(sK6,sK0(sK5,sK6))
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8054,c_2079])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2090,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12929,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12516,c_2090])).

cnf(c_13251,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12929,c_35,c_38,c_40,c_2880,c_3785])).

cnf(c_13253,plain,
    ( k1_relat_1(sK5) != sK3
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2763,c_13251])).

cnf(c_13254,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13253,c_2826])).

cnf(c_27,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2080,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13296,plain,
    ( sK4 = k1_xboole_0
    | r2_relset_1(sK3,sK4,sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_2080])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK1(X0,X1,X2,X3),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2084,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4191,plain,
    ( k1_funct_1(sK6,sK1(sK3,X0,X1,X2)) = k1_funct_1(sK5,sK1(sK3,X0,X1,X2))
    | r2_relset_1(sK3,X0,X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_2079])).

cnf(c_4680,plain,
    ( k1_funct_1(sK5,sK1(sK3,sK4,sK5,X0)) = k1_funct_1(sK6,sK1(sK3,sK4,sK5,X0))
    | r2_relset_1(sK3,sK4,sK5,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_4191])).

cnf(c_4826,plain,
    ( k1_funct_1(sK6,sK1(sK3,sK4,sK5,sK5)) = k1_funct_1(sK5,sK1(sK3,sK4,sK5,sK5))
    | r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_4680])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2683,plain,
    ( r2_relset_1(sK3,sK4,X0,sK5)
    | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),X0)
    | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3626,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_3627,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3626])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2684,plain,
    ( r2_relset_1(sK3,sK4,X0,sK5)
    | r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),X0)
    | r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3636,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5)
    | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_3637,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3636])).

cnf(c_5068,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4826,c_37,c_3627,c_3637])).

cnf(c_13457,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13296,c_37,c_3627,c_3637])).

cnf(c_13510,plain,
    ( r2_relset_1(sK3,k1_xboole_0,sK5,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13457,c_5068])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2092,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3288,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_2092])).

cnf(c_13529,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13457,c_3288])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13547,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13529,c_3])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2095,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3286,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2095,c_2092])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2097,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4296,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3286,c_2097])).

cnf(c_14488,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13547,c_4296])).

cnf(c_14493,plain,
    ( r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13510,c_14488])).

cnf(c_14494,plain,
    ( r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14493])).

cnf(c_13540,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13457,c_2078])).

cnf(c_13543,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13540,c_3])).

cnf(c_13541,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13457,c_2076])).

cnf(c_13542,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13541,c_3])).

cnf(c_7370,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7371,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7370])).

cnf(c_7373,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7371])).

cnf(c_6216,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6217,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6216])).

cnf(c_6219,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6217])).

cnf(c_5053,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5054,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5053])).

cnf(c_3759,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3760,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3759])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2908,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_2910,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_1437,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2461,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_2415,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2416,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_2418,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_2406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6))
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2407,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(X0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_2409,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_2281,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2282,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2281])).

cnf(c_2284,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19607,c_14494,c_13543,c_13542,c_13296,c_7373,c_6219,c_5068,c_5054,c_3760,c_2910,c_2461,c_2418,c_2409,c_2284,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.80/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/1.52  
% 7.80/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.52  
% 7.80/1.52  ------  iProver source info
% 7.80/1.52  
% 7.80/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.52  git: non_committed_changes: false
% 7.80/1.52  git: last_make_outside_of_git: false
% 7.80/1.52  
% 7.80/1.52  ------ 
% 7.80/1.52  
% 7.80/1.52  ------ Input Options
% 7.80/1.52  
% 7.80/1.52  --out_options                           all
% 7.80/1.52  --tptp_safe_out                         true
% 7.80/1.52  --problem_path                          ""
% 7.80/1.52  --include_path                          ""
% 7.80/1.52  --clausifier                            res/vclausify_rel
% 7.80/1.52  --clausifier_options                    ""
% 7.80/1.52  --stdin                                 false
% 7.80/1.52  --stats_out                             all
% 7.80/1.52  
% 7.80/1.52  ------ General Options
% 7.80/1.52  
% 7.80/1.52  --fof                                   false
% 7.80/1.52  --time_out_real                         305.
% 7.80/1.52  --time_out_virtual                      -1.
% 7.80/1.52  --symbol_type_check                     false
% 7.80/1.52  --clausify_out                          false
% 7.80/1.52  --sig_cnt_out                           false
% 7.80/1.52  --trig_cnt_out                          false
% 7.80/1.52  --trig_cnt_out_tolerance                1.
% 7.80/1.52  --trig_cnt_out_sk_spl                   false
% 7.80/1.52  --abstr_cl_out                          false
% 7.80/1.52  
% 7.80/1.52  ------ Global Options
% 7.80/1.52  
% 7.80/1.52  --schedule                              default
% 7.80/1.52  --add_important_lit                     false
% 7.80/1.52  --prop_solver_per_cl                    1000
% 7.80/1.52  --min_unsat_core                        false
% 7.80/1.52  --soft_assumptions                      false
% 7.80/1.52  --soft_lemma_size                       3
% 7.80/1.52  --prop_impl_unit_size                   0
% 7.80/1.52  --prop_impl_unit                        []
% 7.80/1.52  --share_sel_clauses                     true
% 7.80/1.52  --reset_solvers                         false
% 7.80/1.52  --bc_imp_inh                            [conj_cone]
% 7.80/1.52  --conj_cone_tolerance                   3.
% 7.80/1.52  --extra_neg_conj                        none
% 7.80/1.52  --large_theory_mode                     true
% 7.80/1.52  --prolific_symb_bound                   200
% 7.80/1.52  --lt_threshold                          2000
% 7.80/1.52  --clause_weak_htbl                      true
% 7.80/1.52  --gc_record_bc_elim                     false
% 7.80/1.52  
% 7.80/1.52  ------ Preprocessing Options
% 7.80/1.52  
% 7.80/1.52  --preprocessing_flag                    true
% 7.80/1.52  --time_out_prep_mult                    0.1
% 7.80/1.52  --splitting_mode                        input
% 7.80/1.52  --splitting_grd                         true
% 7.80/1.52  --splitting_cvd                         false
% 7.80/1.52  --splitting_cvd_svl                     false
% 7.80/1.52  --splitting_nvd                         32
% 7.80/1.52  --sub_typing                            true
% 7.80/1.52  --prep_gs_sim                           true
% 7.80/1.52  --prep_unflatten                        true
% 7.80/1.52  --prep_res_sim                          true
% 7.80/1.52  --prep_upred                            true
% 7.80/1.52  --prep_sem_filter                       exhaustive
% 7.80/1.52  --prep_sem_filter_out                   false
% 7.80/1.52  --pred_elim                             true
% 7.80/1.52  --res_sim_input                         true
% 7.80/1.52  --eq_ax_congr_red                       true
% 7.80/1.52  --pure_diseq_elim                       true
% 7.80/1.52  --brand_transform                       false
% 7.80/1.52  --non_eq_to_eq                          false
% 7.80/1.52  --prep_def_merge                        true
% 7.80/1.52  --prep_def_merge_prop_impl              false
% 7.80/1.52  --prep_def_merge_mbd                    true
% 7.80/1.52  --prep_def_merge_tr_red                 false
% 7.80/1.52  --prep_def_merge_tr_cl                  false
% 7.80/1.52  --smt_preprocessing                     true
% 7.80/1.52  --smt_ac_axioms                         fast
% 7.80/1.52  --preprocessed_out                      false
% 7.80/1.52  --preprocessed_stats                    false
% 7.80/1.52  
% 7.80/1.52  ------ Abstraction refinement Options
% 7.80/1.52  
% 7.80/1.52  --abstr_ref                             []
% 7.80/1.52  --abstr_ref_prep                        false
% 7.80/1.52  --abstr_ref_until_sat                   false
% 7.80/1.52  --abstr_ref_sig_restrict                funpre
% 7.80/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.52  --abstr_ref_under                       []
% 7.80/1.52  
% 7.80/1.52  ------ SAT Options
% 7.80/1.52  
% 7.80/1.52  --sat_mode                              false
% 7.80/1.52  --sat_fm_restart_options                ""
% 7.80/1.52  --sat_gr_def                            false
% 7.80/1.52  --sat_epr_types                         true
% 7.80/1.52  --sat_non_cyclic_types                  false
% 7.80/1.52  --sat_finite_models                     false
% 7.80/1.52  --sat_fm_lemmas                         false
% 7.80/1.52  --sat_fm_prep                           false
% 7.80/1.52  --sat_fm_uc_incr                        true
% 7.80/1.52  --sat_out_model                         small
% 7.80/1.52  --sat_out_clauses                       false
% 7.80/1.52  
% 7.80/1.52  ------ QBF Options
% 7.80/1.52  
% 7.80/1.52  --qbf_mode                              false
% 7.80/1.52  --qbf_elim_univ                         false
% 7.80/1.52  --qbf_dom_inst                          none
% 7.80/1.52  --qbf_dom_pre_inst                      false
% 7.80/1.52  --qbf_sk_in                             false
% 7.80/1.52  --qbf_pred_elim                         true
% 7.80/1.52  --qbf_split                             512
% 7.80/1.52  
% 7.80/1.52  ------ BMC1 Options
% 7.80/1.52  
% 7.80/1.52  --bmc1_incremental                      false
% 7.80/1.52  --bmc1_axioms                           reachable_all
% 7.80/1.52  --bmc1_min_bound                        0
% 7.80/1.52  --bmc1_max_bound                        -1
% 7.80/1.52  --bmc1_max_bound_default                -1
% 7.80/1.52  --bmc1_symbol_reachability              true
% 7.80/1.52  --bmc1_property_lemmas                  false
% 7.80/1.52  --bmc1_k_induction                      false
% 7.80/1.52  --bmc1_non_equiv_states                 false
% 7.80/1.52  --bmc1_deadlock                         false
% 7.80/1.52  --bmc1_ucm                              false
% 7.80/1.52  --bmc1_add_unsat_core                   none
% 7.80/1.52  --bmc1_unsat_core_children              false
% 7.80/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.52  --bmc1_out_stat                         full
% 7.80/1.52  --bmc1_ground_init                      false
% 7.80/1.52  --bmc1_pre_inst_next_state              false
% 7.80/1.52  --bmc1_pre_inst_state                   false
% 7.80/1.52  --bmc1_pre_inst_reach_state             false
% 7.80/1.52  --bmc1_out_unsat_core                   false
% 7.80/1.52  --bmc1_aig_witness_out                  false
% 7.80/1.52  --bmc1_verbose                          false
% 7.80/1.52  --bmc1_dump_clauses_tptp                false
% 7.80/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.52  --bmc1_dump_file                        -
% 7.80/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.52  --bmc1_ucm_extend_mode                  1
% 7.80/1.52  --bmc1_ucm_init_mode                    2
% 7.80/1.52  --bmc1_ucm_cone_mode                    none
% 7.80/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.52  --bmc1_ucm_relax_model                  4
% 7.80/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.52  --bmc1_ucm_layered_model                none
% 7.80/1.52  --bmc1_ucm_max_lemma_size               10
% 7.80/1.52  
% 7.80/1.52  ------ AIG Options
% 7.80/1.52  
% 7.80/1.52  --aig_mode                              false
% 7.80/1.52  
% 7.80/1.52  ------ Instantiation Options
% 7.80/1.52  
% 7.80/1.52  --instantiation_flag                    true
% 7.80/1.52  --inst_sos_flag                         true
% 7.80/1.52  --inst_sos_phase                        true
% 7.80/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.52  --inst_lit_sel_side                     num_symb
% 7.80/1.52  --inst_solver_per_active                1400
% 7.80/1.52  --inst_solver_calls_frac                1.
% 7.80/1.52  --inst_passive_queue_type               priority_queues
% 7.80/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.52  --inst_passive_queues_freq              [25;2]
% 7.80/1.52  --inst_dismatching                      true
% 7.80/1.52  --inst_eager_unprocessed_to_passive     true
% 7.80/1.52  --inst_prop_sim_given                   true
% 7.80/1.52  --inst_prop_sim_new                     false
% 7.80/1.52  --inst_subs_new                         false
% 7.80/1.52  --inst_eq_res_simp                      false
% 7.80/1.52  --inst_subs_given                       false
% 7.80/1.52  --inst_orphan_elimination               true
% 7.80/1.52  --inst_learning_loop_flag               true
% 7.80/1.52  --inst_learning_start                   3000
% 7.80/1.52  --inst_learning_factor                  2
% 7.80/1.52  --inst_start_prop_sim_after_learn       3
% 7.80/1.52  --inst_sel_renew                        solver
% 7.80/1.52  --inst_lit_activity_flag                true
% 7.80/1.52  --inst_restr_to_given                   false
% 7.80/1.52  --inst_activity_threshold               500
% 7.80/1.52  --inst_out_proof                        true
% 7.80/1.52  
% 7.80/1.52  ------ Resolution Options
% 7.80/1.52  
% 7.80/1.52  --resolution_flag                       true
% 7.80/1.52  --res_lit_sel                           adaptive
% 7.80/1.52  --res_lit_sel_side                      none
% 7.80/1.52  --res_ordering                          kbo
% 7.80/1.52  --res_to_prop_solver                    active
% 7.80/1.52  --res_prop_simpl_new                    false
% 7.80/1.52  --res_prop_simpl_given                  true
% 7.80/1.52  --res_passive_queue_type                priority_queues
% 7.80/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.52  --res_passive_queues_freq               [15;5]
% 7.80/1.52  --res_forward_subs                      full
% 7.80/1.52  --res_backward_subs                     full
% 7.80/1.52  --res_forward_subs_resolution           true
% 7.80/1.52  --res_backward_subs_resolution          true
% 7.80/1.52  --res_orphan_elimination                true
% 7.80/1.52  --res_time_limit                        2.
% 7.80/1.52  --res_out_proof                         true
% 7.80/1.52  
% 7.80/1.52  ------ Superposition Options
% 7.80/1.52  
% 7.80/1.52  --superposition_flag                    true
% 7.80/1.52  --sup_passive_queue_type                priority_queues
% 7.80/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.52  --demod_completeness_check              fast
% 7.80/1.52  --demod_use_ground                      true
% 7.80/1.52  --sup_to_prop_solver                    passive
% 7.80/1.52  --sup_prop_simpl_new                    true
% 7.80/1.52  --sup_prop_simpl_given                  true
% 7.80/1.52  --sup_fun_splitting                     true
% 7.80/1.52  --sup_smt_interval                      50000
% 7.80/1.52  
% 7.80/1.52  ------ Superposition Simplification Setup
% 7.80/1.52  
% 7.80/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.52  --sup_immed_triv                        [TrivRules]
% 7.80/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.52  --sup_immed_bw_main                     []
% 7.80/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.52  --sup_input_bw                          []
% 7.80/1.52  
% 7.80/1.52  ------ Combination Options
% 7.80/1.52  
% 7.80/1.52  --comb_res_mult                         3
% 7.80/1.52  --comb_sup_mult                         2
% 7.80/1.52  --comb_inst_mult                        10
% 7.80/1.52  
% 7.80/1.52  ------ Debug Options
% 7.80/1.52  
% 7.80/1.52  --dbg_backtrace                         false
% 7.80/1.52  --dbg_dump_prop_clauses                 false
% 7.80/1.52  --dbg_dump_prop_clauses_file            -
% 7.80/1.52  --dbg_out_stat                          false
% 7.80/1.52  ------ Parsing...
% 7.80/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.52  
% 7.80/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.80/1.52  
% 7.80/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.52  
% 7.80/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.52  ------ Proving...
% 7.80/1.52  ------ Problem Properties 
% 7.80/1.52  
% 7.80/1.52  
% 7.80/1.52  clauses                                 32
% 7.80/1.52  conjectures                             6
% 7.80/1.52  EPR                                     6
% 7.80/1.52  Horn                                    23
% 7.80/1.52  unary                                   9
% 7.80/1.52  binary                                  8
% 7.80/1.52  lits                                    94
% 7.80/1.52  lits eq                                 27
% 7.80/1.52  fd_pure                                 0
% 7.80/1.52  fd_pseudo                               0
% 7.80/1.52  fd_cond                                 1
% 7.80/1.52  fd_pseudo_cond                          3
% 7.80/1.52  AC symbols                              0
% 7.80/1.52  
% 7.80/1.52  ------ Schedule dynamic 5 is on 
% 7.80/1.52  
% 7.80/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.80/1.52  
% 7.80/1.52  
% 7.80/1.52  ------ 
% 7.80/1.52  Current options:
% 7.80/1.52  ------ 
% 7.80/1.52  
% 7.80/1.52  ------ Input Options
% 7.80/1.52  
% 7.80/1.52  --out_options                           all
% 7.80/1.52  --tptp_safe_out                         true
% 7.80/1.52  --problem_path                          ""
% 7.80/1.52  --include_path                          ""
% 7.80/1.52  --clausifier                            res/vclausify_rel
% 7.80/1.52  --clausifier_options                    ""
% 7.80/1.52  --stdin                                 false
% 7.80/1.52  --stats_out                             all
% 7.80/1.52  
% 7.80/1.52  ------ General Options
% 7.80/1.52  
% 7.80/1.52  --fof                                   false
% 7.80/1.52  --time_out_real                         305.
% 7.80/1.52  --time_out_virtual                      -1.
% 7.80/1.53  --symbol_type_check                     false
% 7.80/1.53  --clausify_out                          false
% 7.80/1.53  --sig_cnt_out                           false
% 7.80/1.53  --trig_cnt_out                          false
% 7.80/1.53  --trig_cnt_out_tolerance                1.
% 7.80/1.53  --trig_cnt_out_sk_spl                   false
% 7.80/1.53  --abstr_cl_out                          false
% 7.80/1.53  
% 7.80/1.53  ------ Global Options
% 7.80/1.53  
% 7.80/1.53  --schedule                              default
% 7.80/1.53  --add_important_lit                     false
% 7.80/1.53  --prop_solver_per_cl                    1000
% 7.80/1.53  --min_unsat_core                        false
% 7.80/1.53  --soft_assumptions                      false
% 7.80/1.53  --soft_lemma_size                       3
% 7.80/1.53  --prop_impl_unit_size                   0
% 7.80/1.53  --prop_impl_unit                        []
% 7.80/1.53  --share_sel_clauses                     true
% 7.80/1.53  --reset_solvers                         false
% 7.80/1.53  --bc_imp_inh                            [conj_cone]
% 7.80/1.53  --conj_cone_tolerance                   3.
% 7.80/1.53  --extra_neg_conj                        none
% 7.80/1.53  --large_theory_mode                     true
% 7.80/1.53  --prolific_symb_bound                   200
% 7.80/1.53  --lt_threshold                          2000
% 7.80/1.53  --clause_weak_htbl                      true
% 7.80/1.53  --gc_record_bc_elim                     false
% 7.80/1.53  
% 7.80/1.53  ------ Preprocessing Options
% 7.80/1.53  
% 7.80/1.53  --preprocessing_flag                    true
% 7.80/1.53  --time_out_prep_mult                    0.1
% 7.80/1.53  --splitting_mode                        input
% 7.80/1.53  --splitting_grd                         true
% 7.80/1.53  --splitting_cvd                         false
% 7.80/1.53  --splitting_cvd_svl                     false
% 7.80/1.53  --splitting_nvd                         32
% 7.80/1.53  --sub_typing                            true
% 7.80/1.53  --prep_gs_sim                           true
% 7.80/1.53  --prep_unflatten                        true
% 7.80/1.53  --prep_res_sim                          true
% 7.80/1.53  --prep_upred                            true
% 7.80/1.53  --prep_sem_filter                       exhaustive
% 7.80/1.53  --prep_sem_filter_out                   false
% 7.80/1.53  --pred_elim                             true
% 7.80/1.53  --res_sim_input                         true
% 7.80/1.53  --eq_ax_congr_red                       true
% 7.80/1.53  --pure_diseq_elim                       true
% 7.80/1.53  --brand_transform                       false
% 7.80/1.53  --non_eq_to_eq                          false
% 7.80/1.53  --prep_def_merge                        true
% 7.80/1.53  --prep_def_merge_prop_impl              false
% 7.80/1.53  --prep_def_merge_mbd                    true
% 7.80/1.53  --prep_def_merge_tr_red                 false
% 7.80/1.53  --prep_def_merge_tr_cl                  false
% 7.80/1.53  --smt_preprocessing                     true
% 7.80/1.53  --smt_ac_axioms                         fast
% 7.80/1.53  --preprocessed_out                      false
% 7.80/1.53  --preprocessed_stats                    false
% 7.80/1.53  
% 7.80/1.53  ------ Abstraction refinement Options
% 7.80/1.53  
% 7.80/1.53  --abstr_ref                             []
% 7.80/1.53  --abstr_ref_prep                        false
% 7.80/1.53  --abstr_ref_until_sat                   false
% 7.80/1.53  --abstr_ref_sig_restrict                funpre
% 7.80/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.53  --abstr_ref_under                       []
% 7.80/1.53  
% 7.80/1.53  ------ SAT Options
% 7.80/1.53  
% 7.80/1.53  --sat_mode                              false
% 7.80/1.53  --sat_fm_restart_options                ""
% 7.80/1.53  --sat_gr_def                            false
% 7.80/1.53  --sat_epr_types                         true
% 7.80/1.53  --sat_non_cyclic_types                  false
% 7.80/1.53  --sat_finite_models                     false
% 7.80/1.53  --sat_fm_lemmas                         false
% 7.80/1.53  --sat_fm_prep                           false
% 7.80/1.53  --sat_fm_uc_incr                        true
% 7.80/1.53  --sat_out_model                         small
% 7.80/1.53  --sat_out_clauses                       false
% 7.80/1.53  
% 7.80/1.53  ------ QBF Options
% 7.80/1.53  
% 7.80/1.53  --qbf_mode                              false
% 7.80/1.53  --qbf_elim_univ                         false
% 7.80/1.53  --qbf_dom_inst                          none
% 7.80/1.53  --qbf_dom_pre_inst                      false
% 7.80/1.53  --qbf_sk_in                             false
% 7.80/1.53  --qbf_pred_elim                         true
% 7.80/1.53  --qbf_split                             512
% 7.80/1.53  
% 7.80/1.53  ------ BMC1 Options
% 7.80/1.53  
% 7.80/1.53  --bmc1_incremental                      false
% 7.80/1.53  --bmc1_axioms                           reachable_all
% 7.80/1.53  --bmc1_min_bound                        0
% 7.80/1.53  --bmc1_max_bound                        -1
% 7.80/1.53  --bmc1_max_bound_default                -1
% 7.80/1.53  --bmc1_symbol_reachability              true
% 7.80/1.53  --bmc1_property_lemmas                  false
% 7.80/1.53  --bmc1_k_induction                      false
% 7.80/1.53  --bmc1_non_equiv_states                 false
% 7.80/1.53  --bmc1_deadlock                         false
% 7.80/1.53  --bmc1_ucm                              false
% 7.80/1.53  --bmc1_add_unsat_core                   none
% 7.80/1.53  --bmc1_unsat_core_children              false
% 7.80/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.53  --bmc1_out_stat                         full
% 7.80/1.53  --bmc1_ground_init                      false
% 7.80/1.53  --bmc1_pre_inst_next_state              false
% 7.80/1.53  --bmc1_pre_inst_state                   false
% 7.80/1.53  --bmc1_pre_inst_reach_state             false
% 7.80/1.53  --bmc1_out_unsat_core                   false
% 7.80/1.53  --bmc1_aig_witness_out                  false
% 7.80/1.53  --bmc1_verbose                          false
% 7.80/1.53  --bmc1_dump_clauses_tptp                false
% 7.80/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.53  --bmc1_dump_file                        -
% 7.80/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.53  --bmc1_ucm_extend_mode                  1
% 7.80/1.53  --bmc1_ucm_init_mode                    2
% 7.80/1.53  --bmc1_ucm_cone_mode                    none
% 7.80/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.53  --bmc1_ucm_relax_model                  4
% 7.80/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.53  --bmc1_ucm_layered_model                none
% 7.80/1.53  --bmc1_ucm_max_lemma_size               10
% 7.80/1.53  
% 7.80/1.53  ------ AIG Options
% 7.80/1.53  
% 7.80/1.53  --aig_mode                              false
% 7.80/1.53  
% 7.80/1.53  ------ Instantiation Options
% 7.80/1.53  
% 7.80/1.53  --instantiation_flag                    true
% 7.80/1.53  --inst_sos_flag                         true
% 7.80/1.53  --inst_sos_phase                        true
% 7.80/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.53  --inst_lit_sel_side                     none
% 7.80/1.53  --inst_solver_per_active                1400
% 7.80/1.53  --inst_solver_calls_frac                1.
% 7.80/1.53  --inst_passive_queue_type               priority_queues
% 7.80/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.53  --inst_passive_queues_freq              [25;2]
% 7.80/1.53  --inst_dismatching                      true
% 7.80/1.53  --inst_eager_unprocessed_to_passive     true
% 7.80/1.53  --inst_prop_sim_given                   true
% 7.80/1.53  --inst_prop_sim_new                     false
% 7.80/1.53  --inst_subs_new                         false
% 7.80/1.53  --inst_eq_res_simp                      false
% 7.80/1.53  --inst_subs_given                       false
% 7.80/1.53  --inst_orphan_elimination               true
% 7.80/1.53  --inst_learning_loop_flag               true
% 7.80/1.53  --inst_learning_start                   3000
% 7.80/1.53  --inst_learning_factor                  2
% 7.80/1.53  --inst_start_prop_sim_after_learn       3
% 7.80/1.53  --inst_sel_renew                        solver
% 7.80/1.53  --inst_lit_activity_flag                true
% 7.80/1.53  --inst_restr_to_given                   false
% 7.80/1.53  --inst_activity_threshold               500
% 7.80/1.53  --inst_out_proof                        true
% 7.80/1.53  
% 7.80/1.53  ------ Resolution Options
% 7.80/1.53  
% 7.80/1.53  --resolution_flag                       false
% 7.80/1.53  --res_lit_sel                           adaptive
% 7.80/1.53  --res_lit_sel_side                      none
% 7.80/1.53  --res_ordering                          kbo
% 7.80/1.53  --res_to_prop_solver                    active
% 7.80/1.53  --res_prop_simpl_new                    false
% 7.80/1.53  --res_prop_simpl_given                  true
% 7.80/1.53  --res_passive_queue_type                priority_queues
% 7.80/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.53  --res_passive_queues_freq               [15;5]
% 7.80/1.53  --res_forward_subs                      full
% 7.80/1.53  --res_backward_subs                     full
% 7.80/1.53  --res_forward_subs_resolution           true
% 7.80/1.53  --res_backward_subs_resolution          true
% 7.80/1.53  --res_orphan_elimination                true
% 7.80/1.53  --res_time_limit                        2.
% 7.80/1.53  --res_out_proof                         true
% 7.80/1.53  
% 7.80/1.53  ------ Superposition Options
% 7.80/1.53  
% 7.80/1.53  --superposition_flag                    true
% 7.80/1.53  --sup_passive_queue_type                priority_queues
% 7.80/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.53  --demod_completeness_check              fast
% 7.80/1.53  --demod_use_ground                      true
% 7.80/1.53  --sup_to_prop_solver                    passive
% 7.80/1.53  --sup_prop_simpl_new                    true
% 7.80/1.53  --sup_prop_simpl_given                  true
% 7.80/1.53  --sup_fun_splitting                     true
% 7.80/1.53  --sup_smt_interval                      50000
% 7.80/1.53  
% 7.80/1.53  ------ Superposition Simplification Setup
% 7.80/1.53  
% 7.80/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.53  --sup_immed_triv                        [TrivRules]
% 7.80/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.53  --sup_immed_bw_main                     []
% 7.80/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.53  --sup_input_bw                          []
% 7.80/1.53  
% 7.80/1.53  ------ Combination Options
% 7.80/1.53  
% 7.80/1.53  --comb_res_mult                         3
% 7.80/1.53  --comb_sup_mult                         2
% 7.80/1.53  --comb_inst_mult                        10
% 7.80/1.53  
% 7.80/1.53  ------ Debug Options
% 7.80/1.53  
% 7.80/1.53  --dbg_backtrace                         false
% 7.80/1.53  --dbg_dump_prop_clauses                 false
% 7.80/1.53  --dbg_dump_prop_clauses_file            -
% 7.80/1.53  --dbg_out_stat                          false
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  ------ Proving...
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  % SZS status Theorem for theBenchmark.p
% 7.80/1.53  
% 7.80/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.53  
% 7.80/1.53  fof(f11,axiom,(
% 7.80/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f22,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(ennf_transformation,[],[f11])).
% 7.80/1.53  
% 7.80/1.53  fof(f23,plain,(
% 7.80/1.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(flattening,[],[f22])).
% 7.80/1.53  
% 7.80/1.53  fof(f39,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(nnf_transformation,[],[f23])).
% 7.80/1.53  
% 7.80/1.53  fof(f64,plain,(
% 7.80/1.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f39])).
% 7.80/1.53  
% 7.80/1.53  fof(f12,conjecture,(
% 7.80/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f13,negated_conjecture,(
% 7.80/1.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 7.80/1.53    inference(negated_conjecture,[],[f12])).
% 7.80/1.53  
% 7.80/1.53  fof(f24,plain,(
% 7.80/1.53    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.80/1.53    inference(ennf_transformation,[],[f13])).
% 7.80/1.53  
% 7.80/1.53  fof(f25,plain,(
% 7.80/1.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.80/1.53    inference(flattening,[],[f24])).
% 7.80/1.53  
% 7.80/1.53  fof(f41,plain,(
% 7.80/1.53    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 7.80/1.53    introduced(choice_axiom,[])).
% 7.80/1.53  
% 7.80/1.53  fof(f40,plain,(
% 7.80/1.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 7.80/1.53    introduced(choice_axiom,[])).
% 7.80/1.53  
% 7.80/1.53  fof(f42,plain,(
% 7.80/1.53    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 7.80/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f41,f40])).
% 7.80/1.53  
% 7.80/1.53  fof(f74,plain,(
% 7.80/1.53    v1_funct_2(sK6,sK3,sK4)),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f75,plain,(
% 7.80/1.53    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f10,axiom,(
% 7.80/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f21,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(ennf_transformation,[],[f10])).
% 7.80/1.53  
% 7.80/1.53  fof(f63,plain,(
% 7.80/1.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f21])).
% 7.80/1.53  
% 7.80/1.53  fof(f71,plain,(
% 7.80/1.53    v1_funct_2(sK5,sK3,sK4)),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f72,plain,(
% 7.80/1.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f7,axiom,(
% 7.80/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f17,plain,(
% 7.80/1.53    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.80/1.53    inference(ennf_transformation,[],[f7])).
% 7.80/1.53  
% 7.80/1.53  fof(f18,plain,(
% 7.80/1.53    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.80/1.53    inference(flattening,[],[f17])).
% 7.80/1.53  
% 7.80/1.53  fof(f31,plain,(
% 7.80/1.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.80/1.53    introduced(choice_axiom,[])).
% 7.80/1.53  
% 7.80/1.53  fof(f32,plain,(
% 7.80/1.53    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.80/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).
% 7.80/1.53  
% 7.80/1.53  fof(f54,plain,(
% 7.80/1.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.53    inference(cnf_transformation,[],[f32])).
% 7.80/1.53  
% 7.80/1.53  fof(f73,plain,(
% 7.80/1.53    v1_funct_1(sK6)),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f8,axiom,(
% 7.80/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f19,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(ennf_transformation,[],[f8])).
% 7.80/1.53  
% 7.80/1.53  fof(f56,plain,(
% 7.80/1.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f19])).
% 7.80/1.53  
% 7.80/1.53  fof(f70,plain,(
% 7.80/1.53    v1_funct_1(sK5)),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f4,axiom,(
% 7.80/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f14,plain,(
% 7.80/1.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.80/1.53    inference(ennf_transformation,[],[f4])).
% 7.80/1.53  
% 7.80/1.53  fof(f50,plain,(
% 7.80/1.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.80/1.53    inference(cnf_transformation,[],[f14])).
% 7.80/1.53  
% 7.80/1.53  fof(f76,plain,(
% 7.80/1.53    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f55,plain,(
% 7.80/1.53    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.53    inference(cnf_transformation,[],[f32])).
% 7.80/1.53  
% 7.80/1.53  fof(f77,plain,(
% 7.80/1.53    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 7.80/1.53    inference(cnf_transformation,[],[f42])).
% 7.80/1.53  
% 7.80/1.53  fof(f9,axiom,(
% 7.80/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f20,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(ennf_transformation,[],[f9])).
% 7.80/1.53  
% 7.80/1.53  fof(f33,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(nnf_transformation,[],[f20])).
% 7.80/1.53  
% 7.80/1.53  fof(f34,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(flattening,[],[f33])).
% 7.80/1.53  
% 7.80/1.53  fof(f35,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(rectify,[],[f34])).
% 7.80/1.53  
% 7.80/1.53  fof(f37,plain,(
% 7.80/1.53    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK2(X0,X1,X2,X3)),X2)) & m1_subset_1(sK2(X0,X1,X2,X3),X1)))) )),
% 7.80/1.53    introduced(choice_axiom,[])).
% 7.80/1.53  
% 7.80/1.53  fof(f36,plain,(
% 7.80/1.53    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK1(X0,X1,X2,X3),X0)))),
% 7.80/1.53    introduced(choice_axiom,[])).
% 7.80/1.53  
% 7.80/1.53  fof(f38,plain,(
% 7.80/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)) & m1_subset_1(sK2(X0,X1,X2,X3),X1)) & m1_subset_1(sK1(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 7.80/1.53  
% 7.80/1.53  fof(f59,plain,(
% 7.80/1.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | m1_subset_1(sK1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f38])).
% 7.80/1.53  
% 7.80/1.53  fof(f62,plain,(
% 7.80/1.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f38])).
% 7.80/1.53  
% 7.80/1.53  fof(f61,plain,(
% 7.80/1.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f38])).
% 7.80/1.53  
% 7.80/1.53  fof(f5,axiom,(
% 7.80/1.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f30,plain,(
% 7.80/1.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.80/1.53    inference(nnf_transformation,[],[f5])).
% 7.80/1.53  
% 7.80/1.53  fof(f51,plain,(
% 7.80/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f30])).
% 7.80/1.53  
% 7.80/1.53  fof(f2,axiom,(
% 7.80/1.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f28,plain,(
% 7.80/1.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.80/1.53    inference(nnf_transformation,[],[f2])).
% 7.80/1.53  
% 7.80/1.53  fof(f29,plain,(
% 7.80/1.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.80/1.53    inference(flattening,[],[f28])).
% 7.80/1.53  
% 7.80/1.53  fof(f48,plain,(
% 7.80/1.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.80/1.53    inference(cnf_transformation,[],[f29])).
% 7.80/1.53  
% 7.80/1.53  fof(f80,plain,(
% 7.80/1.53    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.80/1.53    inference(equality_resolution,[],[f48])).
% 7.80/1.53  
% 7.80/1.53  fof(f3,axiom,(
% 7.80/1.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f49,plain,(
% 7.80/1.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.80/1.53    inference(cnf_transformation,[],[f3])).
% 7.80/1.53  
% 7.80/1.53  fof(f1,axiom,(
% 7.80/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.53  
% 7.80/1.53  fof(f26,plain,(
% 7.80/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.53    inference(nnf_transformation,[],[f1])).
% 7.80/1.53  
% 7.80/1.53  fof(f27,plain,(
% 7.80/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.53    inference(flattening,[],[f26])).
% 7.80/1.53  
% 7.80/1.53  fof(f45,plain,(
% 7.80/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.80/1.53    inference(cnf_transformation,[],[f27])).
% 7.80/1.53  
% 7.80/1.53  cnf(c_1445,plain,
% 7.80/1.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.80/1.53      | r2_relset_1(X4,X5,X6,X7)
% 7.80/1.53      | X4 != X0
% 7.80/1.53      | X5 != X1
% 7.80/1.53      | X6 != X2
% 7.80/1.53      | X7 != X3 ),
% 7.80/1.53      theory(equality) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2151,plain,
% 7.80/1.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.80/1.53      | r2_relset_1(sK3,sK4,sK5,sK6)
% 7.80/1.53      | sK6 != X3
% 7.80/1.53      | sK5 != X2
% 7.80/1.53      | sK4 != X1
% 7.80/1.53      | sK3 != X0 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_19605,plain,
% 7.80/1.53      ( ~ r2_relset_1(sK3,X0,X1,X2)
% 7.80/1.53      | r2_relset_1(sK3,sK4,sK5,sK6)
% 7.80/1.53      | sK6 != X2
% 7.80/1.53      | sK5 != X1
% 7.80/1.53      | sK4 != X0
% 7.80/1.53      | sK3 != sK3 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2151]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_19607,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK6)
% 7.80/1.53      | ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.80/1.53      | sK6 != k1_xboole_0
% 7.80/1.53      | sK5 != k1_xboole_0
% 7.80/1.53      | sK4 != k1_xboole_0
% 7.80/1.53      | sK3 != sK3 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_19605]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_26,plain,
% 7.80/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.80/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.53      | k1_relset_1(X1,X2,X0) = X1
% 7.80/1.53      | k1_xboole_0 = X2 ),
% 7.80/1.53      inference(cnf_transformation,[],[f64]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_30,negated_conjecture,
% 7.80/1.53      ( v1_funct_2(sK6,sK3,sK4) ),
% 7.80/1.53      inference(cnf_transformation,[],[f74]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_500,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.53      | k1_relset_1(X1,X2,X0) = X1
% 7.80/1.53      | sK6 != X0
% 7.80/1.53      | sK4 != X2
% 7.80/1.53      | sK3 != X1
% 7.80/1.53      | k1_xboole_0 = X2 ),
% 7.80/1.53      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_501,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.80/1.53      | k1_relset_1(sK3,sK4,sK6) = sK3
% 7.80/1.53      | k1_xboole_0 = sK4 ),
% 7.80/1.53      inference(unflattening,[status(thm)],[c_500]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_29,negated_conjecture,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(cnf_transformation,[],[f75]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_503,plain,
% 7.80/1.53      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_501,c_29]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2078,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_20,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.53      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.80/1.53      inference(cnf_transformation,[],[f63]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2081,plain,
% 7.80/1.53      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.80/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2569,plain,
% 7.80/1.53      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2078,c_2081]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2763,plain,
% 7.80/1.53      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_503,c_2569]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_33,negated_conjecture,
% 7.80/1.53      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.80/1.53      inference(cnf_transformation,[],[f71]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_511,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.53      | k1_relset_1(X1,X2,X0) = X1
% 7.80/1.53      | sK5 != X0
% 7.80/1.53      | sK4 != X2
% 7.80/1.53      | sK3 != X1
% 7.80/1.53      | k1_xboole_0 = X2 ),
% 7.80/1.53      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_512,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.80/1.53      | k1_relset_1(sK3,sK4,sK5) = sK3
% 7.80/1.53      | k1_xboole_0 = sK4 ),
% 7.80/1.53      inference(unflattening,[status(thm)],[c_511]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_32,negated_conjecture,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_514,plain,
% 7.80/1.53      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_512,c_32]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2076,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2570,plain,
% 7.80/1.53      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2076,c_2081]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2826,plain,
% 7.80/1.53      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_514,c_2570]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_12,plain,
% 7.80/1.53      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.80/1.53      | ~ v1_relat_1(X1)
% 7.80/1.53      | ~ v1_relat_1(X0)
% 7.80/1.53      | ~ v1_funct_1(X1)
% 7.80/1.53      | ~ v1_funct_1(X0)
% 7.80/1.53      | X1 = X0
% 7.80/1.53      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.80/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2089,plain,
% 7.80/1.53      ( X0 = X1
% 7.80/1.53      | k1_relat_1(X0) != k1_relat_1(X1)
% 7.80/1.53      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.80/1.53      | v1_relat_1(X1) != iProver_top
% 7.80/1.53      | v1_relat_1(X0) != iProver_top
% 7.80/1.53      | v1_funct_1(X0) != iProver_top
% 7.80/1.53      | v1_funct_1(X1) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_4992,plain,
% 7.80/1.53      ( k1_relat_1(X0) != sK3
% 7.80/1.53      | sK6 = X0
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
% 7.80/1.53      | v1_relat_1(X0) != iProver_top
% 7.80/1.53      | v1_relat_1(sK6) != iProver_top
% 7.80/1.53      | v1_funct_1(X0) != iProver_top
% 7.80/1.53      | v1_funct_1(sK6) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2763,c_2089]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_31,negated_conjecture,
% 7.80/1.53      ( v1_funct_1(sK6) ),
% 7.80/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_38,plain,
% 7.80/1.53      ( v1_funct_1(sK6) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_40,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.53      | v1_relat_1(X0) ),
% 7.80/1.53      inference(cnf_transformation,[],[f56]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2504,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.53      | v1_relat_1(sK6) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2879,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.80/1.53      | v1_relat_1(sK6) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2504]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2880,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.80/1.53      | v1_relat_1(sK6) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2879]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7972,plain,
% 7.80/1.53      ( v1_funct_1(X0) != iProver_top
% 7.80/1.53      | k1_relat_1(X0) != sK3
% 7.80/1.53      | sK6 = X0
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
% 7.80/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_4992,c_38,c_40,c_2880]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7973,plain,
% 7.80/1.53      ( k1_relat_1(X0) != sK3
% 7.80/1.53      | sK6 = X0
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
% 7.80/1.53      | v1_relat_1(X0) != iProver_top
% 7.80/1.53      | v1_funct_1(X0) != iProver_top ),
% 7.80/1.53      inference(renaming,[status(thm)],[c_7972]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7979,plain,
% 7.80/1.53      ( sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 7.80/1.53      | v1_relat_1(sK5) != iProver_top
% 7.80/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2826,c_7973]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_34,negated_conjecture,
% 7.80/1.53      ( v1_funct_1(sK5) ),
% 7.80/1.53      inference(cnf_transformation,[],[f70]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_35,plain,
% 7.80/1.53      ( v1_funct_1(sK5) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2088,plain,
% 7.80/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.80/1.53      | v1_relat_1(X0) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3785,plain,
% 7.80/1.53      ( v1_relat_1(sK5) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2076,c_2088]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_8045,plain,
% 7.80/1.53      ( sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_7979,c_35,c_3785]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_8049,plain,
% 7.80/1.53      ( sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | r2_hidden(sK0(sK5,sK6),sK3) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2826,c_8045]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7,plain,
% 7.80/1.53      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.80/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2094,plain,
% 7.80/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.80/1.53      | m1_subset_1(X0,X1) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_8054,plain,
% 7.80/1.53      ( sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | m1_subset_1(sK0(sK5,sK6),sK3) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_8049,c_2094]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_28,negated_conjecture,
% 7.80/1.53      ( ~ m1_subset_1(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 7.80/1.53      inference(cnf_transformation,[],[f76]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2079,plain,
% 7.80/1.53      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 7.80/1.53      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_12516,plain,
% 7.80/1.53      ( k1_funct_1(sK5,sK0(sK5,sK6)) = k1_funct_1(sK6,sK0(sK5,sK6))
% 7.80/1.53      | sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_8054,c_2079]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_11,plain,
% 7.80/1.53      ( ~ v1_relat_1(X0)
% 7.80/1.53      | ~ v1_relat_1(X1)
% 7.80/1.53      | ~ v1_funct_1(X0)
% 7.80/1.53      | ~ v1_funct_1(X1)
% 7.80/1.53      | X0 = X1
% 7.80/1.53      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 7.80/1.53      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 7.80/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2090,plain,
% 7.80/1.53      ( X0 = X1
% 7.80/1.53      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 7.80/1.53      | k1_relat_1(X0) != k1_relat_1(X1)
% 7.80/1.53      | v1_relat_1(X0) != iProver_top
% 7.80/1.53      | v1_relat_1(X1) != iProver_top
% 7.80/1.53      | v1_funct_1(X1) != iProver_top
% 7.80/1.53      | v1_funct_1(X0) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_12929,plain,
% 7.80/1.53      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 7.80/1.53      | sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0
% 7.80/1.53      | v1_relat_1(sK6) != iProver_top
% 7.80/1.53      | v1_relat_1(sK5) != iProver_top
% 7.80/1.53      | v1_funct_1(sK6) != iProver_top
% 7.80/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_12516,c_2090]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13251,plain,
% 7.80/1.53      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 7.80/1.53      | sK6 = sK5
% 7.80/1.53      | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_12929,c_35,c_38,c_40,c_2880,c_3785]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13253,plain,
% 7.80/1.53      ( k1_relat_1(sK5) != sK3 | sK6 = sK5 | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2763,c_13251]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13254,plain,
% 7.80/1.53      ( sK6 = sK5 | sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_13253,c_2826]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_27,negated_conjecture,
% 7.80/1.53      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 7.80/1.53      inference(cnf_transformation,[],[f77]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2080,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13296,plain,
% 7.80/1.53      ( sK4 = k1_xboole_0 | r2_relset_1(sK3,sK4,sK5,sK5) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_13254,c_2080]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_17,plain,
% 7.80/1.53      ( r2_relset_1(X0,X1,X2,X3)
% 7.80/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.53      | m1_subset_1(sK1(X0,X1,X2,X3),X0) ),
% 7.80/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2084,plain,
% 7.80/1.53      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.80/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.53      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.53      | m1_subset_1(sK1(X0,X1,X2,X3),X0) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_4191,plain,
% 7.80/1.53      ( k1_funct_1(sK6,sK1(sK3,X0,X1,X2)) = k1_funct_1(sK5,sK1(sK3,X0,X1,X2))
% 7.80/1.53      | r2_relset_1(sK3,X0,X1,X2) = iProver_top
% 7.80/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.80/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2084,c_2079]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_4680,plain,
% 7.80/1.53      ( k1_funct_1(sK5,sK1(sK3,sK4,sK5,X0)) = k1_funct_1(sK6,sK1(sK3,sK4,sK5,X0))
% 7.80/1.53      | r2_relset_1(sK3,sK4,sK5,X0) = iProver_top
% 7.80/1.53      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2076,c_4191]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_4826,plain,
% 7.80/1.53      ( k1_funct_1(sK6,sK1(sK3,sK4,sK5,sK5)) = k1_funct_1(sK5,sK1(sK3,sK4,sK5,sK5))
% 7.80/1.53      | r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2076,c_4680]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_37,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_14,plain,
% 7.80/1.53      ( r2_relset_1(X0,X1,X2,X3)
% 7.80/1.53      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
% 7.80/1.53      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
% 7.80/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.80/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2683,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,X0,sK5)
% 7.80/1.53      | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),X0)
% 7.80/1.53      | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),sK5)
% 7.80/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.80/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_14]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3626,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK5)
% 7.80/1.53      | ~ r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5)
% 7.80/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2683]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3627,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5) != iProver_top
% 7.80/1.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_3626]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_15,plain,
% 7.80/1.53      ( r2_relset_1(X0,X1,X2,X3)
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X3)
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(X0,X1,X2,X3),sK2(X0,X1,X2,X3)),X2)
% 7.80/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.80/1.53      inference(cnf_transformation,[],[f61]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2684,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,X0,sK5)
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),X0)
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(sK3,sK4,X0,sK5),sK2(sK3,sK4,X0,sK5)),sK5)
% 7.80/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.80/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3636,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK5)
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5)
% 7.80/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2684]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3637,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
% 7.80/1.53      | r2_hidden(k4_tarski(sK1(sK3,sK4,sK5,sK5),sK2(sK3,sK4,sK5,sK5)),sK5) = iProver_top
% 7.80/1.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_3636]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_5068,plain,
% 7.80/1.53      ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_4826,c_37,c_3627,c_3637]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13457,plain,
% 7.80/1.53      ( sK4 = k1_xboole_0 ),
% 7.80/1.53      inference(global_propositional_subsumption,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_13296,c_37,c_3627,c_3637]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13510,plain,
% 7.80/1.53      ( r2_relset_1(sK3,k1_xboole_0,sK5,sK5) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13457,c_5068]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_9,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.80/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2092,plain,
% 7.80/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.80/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3288,plain,
% 7.80/1.53      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2076,c_2092]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13529,plain,
% 7.80/1.53      ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13457,c_3288]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3,plain,
% 7.80/1.53      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.53      inference(cnf_transformation,[],[f80]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13547,plain,
% 7.80/1.53      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13529,c_3]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_6,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.80/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2095,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3286,plain,
% 7.80/1.53      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_2095,c_2092]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_0,plain,
% 7.80/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.80/1.53      inference(cnf_transformation,[],[f45]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2097,plain,
% 7.80/1.53      ( X0 = X1
% 7.80/1.53      | r1_tarski(X0,X1) != iProver_top
% 7.80/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_4296,plain,
% 7.80/1.53      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_3286,c_2097]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_14488,plain,
% 7.80/1.53      ( sK5 = k1_xboole_0 ),
% 7.80/1.53      inference(superposition,[status(thm)],[c_13547,c_4296]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_14493,plain,
% 7.80/1.53      ( r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.80/1.53      inference(light_normalisation,[status(thm)],[c_13510,c_14488]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_14494,plain,
% 7.80/1.53      ( r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 7.80/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_14493]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13540,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13457,c_2078]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13543,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13540,c_3]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13541,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13457,c_2076]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_13542,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.80/1.53      inference(demodulation,[status(thm)],[c_13541,c_3]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7370,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7371,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 7.80/1.53      | r1_tarski(sK5,X0) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_7370]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_7373,plain,
% 7.80/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.80/1.53      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_7371]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_6216,plain,
% 7.80/1.53      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0)) | r1_tarski(sK6,X0) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_6217,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 7.80/1.53      | r1_tarski(sK6,X0) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_6216]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_6219,plain,
% 7.80/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.80/1.53      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_6217]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_5053,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_6]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_5054,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_5053]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3759,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_6]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_3760,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_3759]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2907,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5)) | r1_tarski(X0,sK5) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2908,plain,
% 7.80/1.53      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 7.80/1.53      | r1_tarski(X0,sK5) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2910,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
% 7.80/1.53      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2908]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_1437,plain,( X0 = X0 ),theory(equality) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2461,plain,
% 7.80/1.53      ( sK3 = sK3 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_1437]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2415,plain,
% 7.80/1.53      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_0]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2416,plain,
% 7.80/1.53      ( sK5 = X0
% 7.80/1.53      | r1_tarski(X0,sK5) != iProver_top
% 7.80/1.53      | r1_tarski(sK5,X0) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2418,plain,
% 7.80/1.53      ( sK5 = k1_xboole_0
% 7.80/1.53      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 7.80/1.53      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2416]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2406,plain,
% 7.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6)) | r1_tarski(X0,sK6) ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2407,plain,
% 7.80/1.53      ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
% 7.80/1.53      | r1_tarski(X0,sK6) = iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2409,plain,
% 7.80/1.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6)) != iProver_top
% 7.80/1.53      | r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2407]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2281,plain,
% 7.80/1.53      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_0]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2282,plain,
% 7.80/1.53      ( sK6 = X0
% 7.80/1.53      | r1_tarski(X0,sK6) != iProver_top
% 7.80/1.53      | r1_tarski(sK6,X0) != iProver_top ),
% 7.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2281]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(c_2284,plain,
% 7.80/1.53      ( sK6 = k1_xboole_0
% 7.80/1.53      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 7.80/1.53      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 7.80/1.53      inference(instantiation,[status(thm)],[c_2282]) ).
% 7.80/1.53  
% 7.80/1.53  cnf(contradiction,plain,
% 7.80/1.53      ( $false ),
% 7.80/1.53      inference(minisat,
% 7.80/1.53                [status(thm)],
% 7.80/1.53                [c_19607,c_14494,c_13543,c_13542,c_13296,c_7373,c_6219,
% 7.80/1.53                 c_5068,c_5054,c_3760,c_2910,c_2461,c_2418,c_2409,c_2284,
% 7.80/1.53                 c_27]) ).
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.53  
% 7.80/1.53  ------                               Statistics
% 7.80/1.53  
% 7.80/1.53  ------ General
% 7.80/1.53  
% 7.80/1.53  abstr_ref_over_cycles:                  0
% 7.80/1.53  abstr_ref_under_cycles:                 0
% 7.80/1.53  gc_basic_clause_elim:                   0
% 7.80/1.53  forced_gc_time:                         0
% 7.80/1.53  parsing_time:                           0.01
% 7.80/1.53  unif_index_cands_time:                  0.
% 7.80/1.53  unif_index_add_time:                    0.
% 7.80/1.53  orderings_time:                         0.
% 7.80/1.53  out_proof_time:                         0.011
% 7.80/1.53  total_time:                             0.749
% 7.80/1.53  num_of_symbols:                         52
% 7.80/1.53  num_of_terms:                           22121
% 7.80/1.53  
% 7.80/1.53  ------ Preprocessing
% 7.80/1.53  
% 7.80/1.53  num_of_splits:                          0
% 7.80/1.53  num_of_split_atoms:                     0
% 7.80/1.53  num_of_reused_defs:                     0
% 7.80/1.53  num_eq_ax_congr_red:                    44
% 7.80/1.53  num_of_sem_filtered_clauses:            1
% 7.80/1.53  num_of_subtypes:                        0
% 7.80/1.53  monotx_restored_types:                  0
% 7.80/1.53  sat_num_of_epr_types:                   0
% 7.80/1.53  sat_num_of_non_cyclic_types:            0
% 7.80/1.53  sat_guarded_non_collapsed_types:        0
% 7.80/1.53  num_pure_diseq_elim:                    0
% 7.80/1.53  simp_replaced_by:                       0
% 7.80/1.53  res_preprocessed:                       153
% 7.80/1.53  prep_upred:                             0
% 7.80/1.53  prep_unflattend:                        66
% 7.80/1.53  smt_new_axioms:                         0
% 7.80/1.53  pred_elim_cands:                        6
% 7.80/1.53  pred_elim:                              1
% 7.80/1.53  pred_elim_cl:                           2
% 7.80/1.53  pred_elim_cycles:                       3
% 7.80/1.53  merged_defs:                            8
% 7.80/1.53  merged_defs_ncl:                        0
% 7.80/1.53  bin_hyper_res:                          8
% 7.80/1.53  prep_cycles:                            4
% 7.80/1.53  pred_elim_time:                         0.014
% 7.80/1.53  splitting_time:                         0.
% 7.80/1.53  sem_filter_time:                        0.
% 7.80/1.53  monotx_time:                            0.001
% 7.80/1.53  subtype_inf_time:                       0.
% 7.80/1.53  
% 7.80/1.53  ------ Problem properties
% 7.80/1.53  
% 7.80/1.53  clauses:                                32
% 7.80/1.53  conjectures:                            6
% 7.80/1.53  epr:                                    6
% 7.80/1.53  horn:                                   23
% 7.80/1.53  ground:                                 11
% 7.80/1.53  unary:                                  9
% 7.80/1.53  binary:                                 8
% 7.80/1.53  lits:                                   94
% 7.80/1.53  lits_eq:                                27
% 7.80/1.53  fd_pure:                                0
% 7.80/1.53  fd_pseudo:                              0
% 7.80/1.53  fd_cond:                                1
% 7.80/1.53  fd_pseudo_cond:                         3
% 7.80/1.53  ac_symbols:                             0
% 7.80/1.53  
% 7.80/1.53  ------ Propositional Solver
% 7.80/1.53  
% 7.80/1.53  prop_solver_calls:                      30
% 7.80/1.53  prop_fast_solver_calls:                 3061
% 7.80/1.53  smt_solver_calls:                       0
% 7.80/1.53  smt_fast_solver_calls:                  0
% 7.80/1.53  prop_num_of_clauses:                    7576
% 7.80/1.53  prop_preprocess_simplified:             15970
% 7.80/1.53  prop_fo_subsumed:                       96
% 7.80/1.53  prop_solver_time:                       0.
% 7.80/1.53  smt_solver_time:                        0.
% 7.80/1.53  smt_fast_solver_time:                   0.
% 7.80/1.53  prop_fast_solver_time:                  0.
% 7.80/1.53  prop_unsat_core_time:                   0.
% 7.80/1.53  
% 7.80/1.53  ------ QBF
% 7.80/1.53  
% 7.80/1.53  qbf_q_res:                              0
% 7.80/1.53  qbf_num_tautologies:                    0
% 7.80/1.53  qbf_prep_cycles:                        0
% 7.80/1.53  
% 7.80/1.53  ------ BMC1
% 7.80/1.53  
% 7.80/1.53  bmc1_current_bound:                     -1
% 7.80/1.53  bmc1_last_solved_bound:                 -1
% 7.80/1.53  bmc1_unsat_core_size:                   -1
% 7.80/1.53  bmc1_unsat_core_parents_size:           -1
% 7.80/1.53  bmc1_merge_next_fun:                    0
% 7.80/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.80/1.53  
% 7.80/1.53  ------ Instantiation
% 7.80/1.53  
% 7.80/1.53  inst_num_of_clauses:                    2090
% 7.80/1.53  inst_num_in_passive:                    1028
% 7.80/1.53  inst_num_in_active:                     984
% 7.80/1.53  inst_num_in_unprocessed:                77
% 7.80/1.53  inst_num_of_loops:                      1140
% 7.80/1.53  inst_num_of_learning_restarts:          0
% 7.80/1.53  inst_num_moves_active_passive:          152
% 7.80/1.53  inst_lit_activity:                      0
% 7.80/1.53  inst_lit_activity_moves:                0
% 7.80/1.53  inst_num_tautologies:                   0
% 7.80/1.53  inst_num_prop_implied:                  0
% 7.80/1.53  inst_num_existing_simplified:           0
% 7.80/1.53  inst_num_eq_res_simplified:             0
% 7.80/1.53  inst_num_child_elim:                    0
% 7.80/1.53  inst_num_of_dismatching_blockings:      2763
% 7.80/1.53  inst_num_of_non_proper_insts:           2752
% 7.80/1.53  inst_num_of_duplicates:                 0
% 7.80/1.53  inst_inst_num_from_inst_to_res:         0
% 7.80/1.53  inst_dismatching_checking_time:         0.
% 7.80/1.53  
% 7.80/1.53  ------ Resolution
% 7.80/1.53  
% 7.80/1.53  res_num_of_clauses:                     0
% 7.80/1.53  res_num_in_passive:                     0
% 7.80/1.53  res_num_in_active:                      0
% 7.80/1.53  res_num_of_loops:                       157
% 7.80/1.53  res_forward_subset_subsumed:            165
% 7.80/1.53  res_backward_subset_subsumed:           0
% 7.80/1.53  res_forward_subsumed:                   0
% 7.80/1.53  res_backward_subsumed:                  0
% 7.80/1.53  res_forward_subsumption_resolution:     0
% 7.80/1.53  res_backward_subsumption_resolution:    0
% 7.80/1.53  res_clause_to_clause_subsumption:       3300
% 7.80/1.53  res_orphan_elimination:                 0
% 7.80/1.53  res_tautology_del:                      137
% 7.80/1.53  res_num_eq_res_simplified:              0
% 7.80/1.53  res_num_sel_changes:                    0
% 7.80/1.53  res_moves_from_active_to_pass:          0
% 7.80/1.53  
% 7.80/1.53  ------ Superposition
% 7.80/1.53  
% 7.80/1.53  sup_time_total:                         0.
% 7.80/1.53  sup_time_generating:                    0.
% 7.80/1.53  sup_time_sim_full:                      0.
% 7.80/1.53  sup_time_sim_immed:                     0.
% 7.80/1.53  
% 7.80/1.53  sup_num_of_clauses:                     586
% 7.80/1.53  sup_num_in_active:                      125
% 7.80/1.53  sup_num_in_passive:                     461
% 7.80/1.53  sup_num_of_loops:                       226
% 7.80/1.53  sup_fw_superposition:                   413
% 7.80/1.53  sup_bw_superposition:                   511
% 7.80/1.53  sup_immediate_simplified:               269
% 7.80/1.53  sup_given_eliminated:                   2
% 7.80/1.53  comparisons_done:                       0
% 7.80/1.53  comparisons_avoided:                    45
% 7.80/1.53  
% 7.80/1.53  ------ Simplifications
% 7.80/1.53  
% 7.80/1.53  
% 7.80/1.53  sim_fw_subset_subsumed:                 41
% 7.80/1.53  sim_bw_subset_subsumed:                 31
% 7.80/1.53  sim_fw_subsumed:                        74
% 7.80/1.53  sim_bw_subsumed:                        14
% 7.80/1.53  sim_fw_subsumption_res:                 0
% 7.80/1.53  sim_bw_subsumption_res:                 0
% 7.80/1.53  sim_tautology_del:                      40
% 7.80/1.53  sim_eq_tautology_del:                   120
% 7.80/1.53  sim_eq_res_simp:                        8
% 7.80/1.53  sim_fw_demodulated:                     101
% 7.80/1.53  sim_bw_demodulated:                     85
% 7.80/1.53  sim_light_normalised:                   204
% 7.80/1.53  sim_joinable_taut:                      0
% 7.80/1.53  sim_joinable_simp:                      0
% 7.80/1.53  sim_ac_normalised:                      0
% 7.80/1.53  sim_smt_subsumption:                    0
% 7.80/1.53  
%------------------------------------------------------------------------------
