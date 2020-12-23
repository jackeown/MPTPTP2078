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
% DateTime   : Thu Dec  3 12:07:42 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 840 expanded)
%              Number of clauses        :   83 ( 254 expanded)
%              Number of leaves         :   20 ( 215 expanded)
%              Depth                    :   25
%              Number of atoms          :  589 (5320 expanded)
%              Number of equality atoms :  207 ( 943 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK7)
        & ! [X4] :
            ( k1_funct_1(sK7,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7,X0,X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
          ( ~ r2_relset_1(sK4,sK5,sK6,X3)
          & ! [X4] :
              ( k1_funct_1(sK6,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7)
    & ! [X4] :
        ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
        | ~ m1_subset_1(X4,sK4) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f36,f53,f52])).

fof(f90,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f48,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
            | ~ r2_hidden(k4_tarski(X4,X5),X2) )
          & ( r2_hidden(k4_tarski(X4,X5),X3)
            | r2_hidden(k4_tarski(X4,X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK3(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
            ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK2(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK3(X0,X1,X2,X3),X1)
                & m1_subset_1(sK2(X0,X1,X2,X3),X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
      | ~ m1_subset_1(X4,sK4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_517,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_33])).

cnf(c_2220,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2225,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3289,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2220,c_2225])).

cnf(c_3514,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_517,c_3289])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_526,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_528,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_36])).

cnf(c_2218,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3290,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2218,c_2225])).

cnf(c_3517,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_528,c_3290])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2234,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5710,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_2234])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2558,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2559,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2558])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3783,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2232])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0,X3),sK3(X1,X2,X0,X3)),X3)
    | r2_hidden(k4_tarski(sK2(X1,X2,X0,X3),sK3(X1,X2,X0,X3)),X0)
    | sK7 != X3
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_865,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_867,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_36,c_33])).

cnf(c_869,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3340,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3341,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3340])).

cnf(c_3565,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3566,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3565])).

cnf(c_3784,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_2232])).

cnf(c_3984,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3783,c_869,c_3341,c_3566,c_3784])).

cnf(c_3986,plain,
    ( ~ v1_xboole_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3984])).

cnf(c_1632,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7948,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_7950,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7948])).

cnf(c_13575,plain,
    ( v1_funct_1(X0) != iProver_top
    | sK7 = X0
    | k1_relat_1(X0) != sK4
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5710,c_42,c_44,c_2,c_2559,c_3986,c_7950])).

cnf(c_13576,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13575])).

cnf(c_13587,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_13576])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_892,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK7 != X0
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_893,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | sK6 != sK7 ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_2561,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2562,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2561])).

cnf(c_1630,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4280,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2757,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_3378,plain,
    ( X0 = sK7
    | X0 != sK6
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2757])).

cnf(c_4285,plain,
    ( sK7 != sK6
    | sK6 = sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3378])).

cnf(c_13600,plain,
    ( r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13587,c_39,c_41,c_33,c_2,c_893,c_2562,c_3986,c_4280,c_4285,c_7950])).

cnf(c_13605,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_13600])).

cnf(c_13730,plain,
    ( r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13605,c_2,c_3986,c_7950])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_1])).

cnf(c_234,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_2216,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_13735,plain,
    ( m1_subset_1(sK1(sK6,sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13730,c_2216])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2221,plain,
    ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23740,plain,
    ( k1_funct_1(sK6,sK1(sK6,sK7)) = k1_funct_1(sK7,sK1(sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_13735,c_2221])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2235,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_23852,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_23740,c_2235])).

cnf(c_23855,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23852,c_39,c_41,c_42,c_33,c_44,c_893,c_2559,c_2562,c_4280,c_4285])).

cnf(c_23858,plain,
    ( k1_relat_1(sK6) != sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3514,c_23855])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23858,c_7950,c_3986,c_3517,c_2])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:37:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.99/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/1.49  
% 6.99/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.99/1.49  
% 6.99/1.49  ------  iProver source info
% 6.99/1.49  
% 6.99/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.99/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.99/1.49  git: non_committed_changes: false
% 6.99/1.49  git: last_make_outside_of_git: false
% 6.99/1.49  
% 6.99/1.49  ------ 
% 6.99/1.49  
% 6.99/1.49  ------ Input Options
% 6.99/1.49  
% 6.99/1.49  --out_options                           all
% 6.99/1.49  --tptp_safe_out                         true
% 6.99/1.49  --problem_path                          ""
% 6.99/1.49  --include_path                          ""
% 6.99/1.49  --clausifier                            res/vclausify_rel
% 6.99/1.49  --clausifier_options                    --mode clausify
% 6.99/1.49  --stdin                                 false
% 6.99/1.49  --stats_out                             all
% 6.99/1.49  
% 6.99/1.49  ------ General Options
% 6.99/1.49  
% 6.99/1.49  --fof                                   false
% 6.99/1.49  --time_out_real                         305.
% 6.99/1.49  --time_out_virtual                      -1.
% 6.99/1.49  --symbol_type_check                     false
% 6.99/1.49  --clausify_out                          false
% 6.99/1.49  --sig_cnt_out                           false
% 6.99/1.49  --trig_cnt_out                          false
% 6.99/1.49  --trig_cnt_out_tolerance                1.
% 6.99/1.49  --trig_cnt_out_sk_spl                   false
% 6.99/1.49  --abstr_cl_out                          false
% 6.99/1.49  
% 6.99/1.49  ------ Global Options
% 6.99/1.49  
% 6.99/1.49  --schedule                              default
% 6.99/1.49  --add_important_lit                     false
% 6.99/1.49  --prop_solver_per_cl                    1000
% 6.99/1.49  --min_unsat_core                        false
% 6.99/1.49  --soft_assumptions                      false
% 6.99/1.49  --soft_lemma_size                       3
% 6.99/1.49  --prop_impl_unit_size                   0
% 6.99/1.49  --prop_impl_unit                        []
% 6.99/1.49  --share_sel_clauses                     true
% 6.99/1.49  --reset_solvers                         false
% 6.99/1.49  --bc_imp_inh                            [conj_cone]
% 6.99/1.49  --conj_cone_tolerance                   3.
% 6.99/1.49  --extra_neg_conj                        none
% 6.99/1.49  --large_theory_mode                     true
% 6.99/1.49  --prolific_symb_bound                   200
% 6.99/1.49  --lt_threshold                          2000
% 6.99/1.49  --clause_weak_htbl                      true
% 6.99/1.49  --gc_record_bc_elim                     false
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing Options
% 6.99/1.49  
% 6.99/1.49  --preprocessing_flag                    true
% 6.99/1.49  --time_out_prep_mult                    0.1
% 6.99/1.49  --splitting_mode                        input
% 6.99/1.49  --splitting_grd                         true
% 6.99/1.49  --splitting_cvd                         false
% 6.99/1.49  --splitting_cvd_svl                     false
% 6.99/1.49  --splitting_nvd                         32
% 6.99/1.49  --sub_typing                            true
% 6.99/1.49  --prep_gs_sim                           true
% 6.99/1.49  --prep_unflatten                        true
% 6.99/1.49  --prep_res_sim                          true
% 6.99/1.49  --prep_upred                            true
% 6.99/1.49  --prep_sem_filter                       exhaustive
% 6.99/1.49  --prep_sem_filter_out                   false
% 6.99/1.49  --pred_elim                             true
% 6.99/1.49  --res_sim_input                         true
% 6.99/1.49  --eq_ax_congr_red                       true
% 6.99/1.49  --pure_diseq_elim                       true
% 6.99/1.49  --brand_transform                       false
% 6.99/1.49  --non_eq_to_eq                          false
% 6.99/1.49  --prep_def_merge                        true
% 6.99/1.49  --prep_def_merge_prop_impl              false
% 6.99/1.49  --prep_def_merge_mbd                    true
% 6.99/1.49  --prep_def_merge_tr_red                 false
% 6.99/1.49  --prep_def_merge_tr_cl                  false
% 6.99/1.49  --smt_preprocessing                     true
% 6.99/1.49  --smt_ac_axioms                         fast
% 6.99/1.49  --preprocessed_out                      false
% 6.99/1.49  --preprocessed_stats                    false
% 6.99/1.49  
% 6.99/1.49  ------ Abstraction refinement Options
% 6.99/1.49  
% 6.99/1.49  --abstr_ref                             []
% 6.99/1.49  --abstr_ref_prep                        false
% 6.99/1.49  --abstr_ref_until_sat                   false
% 6.99/1.49  --abstr_ref_sig_restrict                funpre
% 6.99/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.49  --abstr_ref_under                       []
% 6.99/1.49  
% 6.99/1.49  ------ SAT Options
% 6.99/1.49  
% 6.99/1.49  --sat_mode                              false
% 6.99/1.49  --sat_fm_restart_options                ""
% 6.99/1.49  --sat_gr_def                            false
% 6.99/1.49  --sat_epr_types                         true
% 6.99/1.49  --sat_non_cyclic_types                  false
% 6.99/1.49  --sat_finite_models                     false
% 6.99/1.49  --sat_fm_lemmas                         false
% 6.99/1.49  --sat_fm_prep                           false
% 6.99/1.49  --sat_fm_uc_incr                        true
% 6.99/1.49  --sat_out_model                         small
% 6.99/1.49  --sat_out_clauses                       false
% 6.99/1.49  
% 6.99/1.49  ------ QBF Options
% 6.99/1.49  
% 6.99/1.49  --qbf_mode                              false
% 6.99/1.49  --qbf_elim_univ                         false
% 6.99/1.49  --qbf_dom_inst                          none
% 6.99/1.49  --qbf_dom_pre_inst                      false
% 6.99/1.49  --qbf_sk_in                             false
% 6.99/1.49  --qbf_pred_elim                         true
% 6.99/1.49  --qbf_split                             512
% 6.99/1.49  
% 6.99/1.49  ------ BMC1 Options
% 6.99/1.49  
% 6.99/1.49  --bmc1_incremental                      false
% 6.99/1.49  --bmc1_axioms                           reachable_all
% 6.99/1.49  --bmc1_min_bound                        0
% 6.99/1.49  --bmc1_max_bound                        -1
% 6.99/1.49  --bmc1_max_bound_default                -1
% 6.99/1.49  --bmc1_symbol_reachability              true
% 6.99/1.49  --bmc1_property_lemmas                  false
% 6.99/1.49  --bmc1_k_induction                      false
% 6.99/1.49  --bmc1_non_equiv_states                 false
% 6.99/1.49  --bmc1_deadlock                         false
% 6.99/1.49  --bmc1_ucm                              false
% 6.99/1.49  --bmc1_add_unsat_core                   none
% 6.99/1.49  --bmc1_unsat_core_children              false
% 6.99/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.49  --bmc1_out_stat                         full
% 6.99/1.49  --bmc1_ground_init                      false
% 6.99/1.49  --bmc1_pre_inst_next_state              false
% 6.99/1.49  --bmc1_pre_inst_state                   false
% 6.99/1.49  --bmc1_pre_inst_reach_state             false
% 6.99/1.49  --bmc1_out_unsat_core                   false
% 6.99/1.49  --bmc1_aig_witness_out                  false
% 6.99/1.49  --bmc1_verbose                          false
% 6.99/1.49  --bmc1_dump_clauses_tptp                false
% 6.99/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.49  --bmc1_dump_file                        -
% 6.99/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.49  --bmc1_ucm_extend_mode                  1
% 6.99/1.49  --bmc1_ucm_init_mode                    2
% 6.99/1.49  --bmc1_ucm_cone_mode                    none
% 6.99/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.49  --bmc1_ucm_relax_model                  4
% 6.99/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.49  --bmc1_ucm_layered_model                none
% 6.99/1.49  --bmc1_ucm_max_lemma_size               10
% 6.99/1.49  
% 6.99/1.49  ------ AIG Options
% 6.99/1.49  
% 6.99/1.49  --aig_mode                              false
% 6.99/1.49  
% 6.99/1.49  ------ Instantiation Options
% 6.99/1.49  
% 6.99/1.49  --instantiation_flag                    true
% 6.99/1.49  --inst_sos_flag                         false
% 6.99/1.49  --inst_sos_phase                        true
% 6.99/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.49  --inst_lit_sel_side                     num_symb
% 6.99/1.49  --inst_solver_per_active                1400
% 6.99/1.49  --inst_solver_calls_frac                1.
% 6.99/1.49  --inst_passive_queue_type               priority_queues
% 6.99/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.49  --inst_passive_queues_freq              [25;2]
% 6.99/1.49  --inst_dismatching                      true
% 6.99/1.49  --inst_eager_unprocessed_to_passive     true
% 6.99/1.49  --inst_prop_sim_given                   true
% 6.99/1.49  --inst_prop_sim_new                     false
% 6.99/1.49  --inst_subs_new                         false
% 6.99/1.49  --inst_eq_res_simp                      false
% 6.99/1.49  --inst_subs_given                       false
% 6.99/1.49  --inst_orphan_elimination               true
% 6.99/1.49  --inst_learning_loop_flag               true
% 6.99/1.49  --inst_learning_start                   3000
% 6.99/1.49  --inst_learning_factor                  2
% 6.99/1.49  --inst_start_prop_sim_after_learn       3
% 6.99/1.49  --inst_sel_renew                        solver
% 6.99/1.49  --inst_lit_activity_flag                true
% 6.99/1.49  --inst_restr_to_given                   false
% 6.99/1.49  --inst_activity_threshold               500
% 6.99/1.49  --inst_out_proof                        true
% 6.99/1.49  
% 6.99/1.49  ------ Resolution Options
% 6.99/1.49  
% 6.99/1.49  --resolution_flag                       true
% 6.99/1.49  --res_lit_sel                           adaptive
% 6.99/1.49  --res_lit_sel_side                      none
% 6.99/1.49  --res_ordering                          kbo
% 6.99/1.49  --res_to_prop_solver                    active
% 6.99/1.49  --res_prop_simpl_new                    false
% 6.99/1.49  --res_prop_simpl_given                  true
% 6.99/1.49  --res_passive_queue_type                priority_queues
% 6.99/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.49  --res_passive_queues_freq               [15;5]
% 6.99/1.49  --res_forward_subs                      full
% 6.99/1.49  --res_backward_subs                     full
% 6.99/1.49  --res_forward_subs_resolution           true
% 6.99/1.49  --res_backward_subs_resolution          true
% 6.99/1.49  --res_orphan_elimination                true
% 6.99/1.49  --res_time_limit                        2.
% 6.99/1.49  --res_out_proof                         true
% 6.99/1.49  
% 6.99/1.49  ------ Superposition Options
% 6.99/1.49  
% 6.99/1.49  --superposition_flag                    true
% 6.99/1.49  --sup_passive_queue_type                priority_queues
% 6.99/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.49  --demod_completeness_check              fast
% 6.99/1.49  --demod_use_ground                      true
% 6.99/1.49  --sup_to_prop_solver                    passive
% 6.99/1.49  --sup_prop_simpl_new                    true
% 6.99/1.49  --sup_prop_simpl_given                  true
% 6.99/1.49  --sup_fun_splitting                     false
% 6.99/1.49  --sup_smt_interval                      50000
% 6.99/1.49  
% 6.99/1.49  ------ Superposition Simplification Setup
% 6.99/1.49  
% 6.99/1.49  --sup_indices_passive                   []
% 6.99/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_full_bw                           [BwDemod]
% 6.99/1.49  --sup_immed_triv                        [TrivRules]
% 6.99/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_immed_bw_main                     []
% 6.99/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.49  
% 6.99/1.49  ------ Combination Options
% 6.99/1.49  
% 6.99/1.49  --comb_res_mult                         3
% 6.99/1.49  --comb_sup_mult                         2
% 6.99/1.49  --comb_inst_mult                        10
% 6.99/1.49  
% 6.99/1.49  ------ Debug Options
% 6.99/1.49  
% 6.99/1.49  --dbg_backtrace                         false
% 6.99/1.49  --dbg_dump_prop_clauses                 false
% 6.99/1.49  --dbg_dump_prop_clauses_file            -
% 6.99/1.49  --dbg_out_stat                          false
% 6.99/1.49  ------ Parsing...
% 6.99/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.99/1.49  ------ Proving...
% 6.99/1.49  ------ Problem Properties 
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  clauses                                 36
% 6.99/1.49  conjectures                             6
% 6.99/1.49  EPR                                     9
% 6.99/1.49  Horn                                    26
% 6.99/1.49  unary                                   7
% 6.99/1.49  binary                                  10
% 6.99/1.49  lits                                    109
% 6.99/1.49  lits eq                                 23
% 6.99/1.49  fd_pure                                 0
% 6.99/1.49  fd_pseudo                               0
% 6.99/1.49  fd_cond                                 1
% 6.99/1.49  fd_pseudo_cond                          3
% 6.99/1.49  AC symbols                              0
% 6.99/1.49  
% 6.99/1.49  ------ Schedule dynamic 5 is on 
% 6.99/1.49  
% 6.99/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  ------ 
% 6.99/1.49  Current options:
% 6.99/1.49  ------ 
% 6.99/1.49  
% 6.99/1.49  ------ Input Options
% 6.99/1.49  
% 6.99/1.49  --out_options                           all
% 6.99/1.49  --tptp_safe_out                         true
% 6.99/1.49  --problem_path                          ""
% 6.99/1.49  --include_path                          ""
% 6.99/1.49  --clausifier                            res/vclausify_rel
% 6.99/1.49  --clausifier_options                    --mode clausify
% 6.99/1.49  --stdin                                 false
% 6.99/1.49  --stats_out                             all
% 6.99/1.49  
% 6.99/1.49  ------ General Options
% 6.99/1.49  
% 6.99/1.49  --fof                                   false
% 6.99/1.49  --time_out_real                         305.
% 6.99/1.49  --time_out_virtual                      -1.
% 6.99/1.49  --symbol_type_check                     false
% 6.99/1.49  --clausify_out                          false
% 6.99/1.49  --sig_cnt_out                           false
% 6.99/1.49  --trig_cnt_out                          false
% 6.99/1.49  --trig_cnt_out_tolerance                1.
% 6.99/1.49  --trig_cnt_out_sk_spl                   false
% 6.99/1.49  --abstr_cl_out                          false
% 6.99/1.49  
% 6.99/1.49  ------ Global Options
% 6.99/1.49  
% 6.99/1.49  --schedule                              default
% 6.99/1.49  --add_important_lit                     false
% 6.99/1.49  --prop_solver_per_cl                    1000
% 6.99/1.49  --min_unsat_core                        false
% 6.99/1.49  --soft_assumptions                      false
% 6.99/1.49  --soft_lemma_size                       3
% 6.99/1.49  --prop_impl_unit_size                   0
% 6.99/1.49  --prop_impl_unit                        []
% 6.99/1.49  --share_sel_clauses                     true
% 6.99/1.49  --reset_solvers                         false
% 6.99/1.49  --bc_imp_inh                            [conj_cone]
% 6.99/1.49  --conj_cone_tolerance                   3.
% 6.99/1.49  --extra_neg_conj                        none
% 6.99/1.49  --large_theory_mode                     true
% 6.99/1.49  --prolific_symb_bound                   200
% 6.99/1.49  --lt_threshold                          2000
% 6.99/1.49  --clause_weak_htbl                      true
% 6.99/1.49  --gc_record_bc_elim                     false
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing Options
% 6.99/1.49  
% 6.99/1.49  --preprocessing_flag                    true
% 6.99/1.49  --time_out_prep_mult                    0.1
% 6.99/1.49  --splitting_mode                        input
% 6.99/1.49  --splitting_grd                         true
% 6.99/1.49  --splitting_cvd                         false
% 6.99/1.49  --splitting_cvd_svl                     false
% 6.99/1.49  --splitting_nvd                         32
% 6.99/1.49  --sub_typing                            true
% 6.99/1.49  --prep_gs_sim                           true
% 6.99/1.49  --prep_unflatten                        true
% 6.99/1.49  --prep_res_sim                          true
% 6.99/1.49  --prep_upred                            true
% 6.99/1.49  --prep_sem_filter                       exhaustive
% 6.99/1.49  --prep_sem_filter_out                   false
% 6.99/1.49  --pred_elim                             true
% 6.99/1.49  --res_sim_input                         true
% 6.99/1.49  --eq_ax_congr_red                       true
% 6.99/1.49  --pure_diseq_elim                       true
% 6.99/1.49  --brand_transform                       false
% 6.99/1.49  --non_eq_to_eq                          false
% 6.99/1.49  --prep_def_merge                        true
% 6.99/1.49  --prep_def_merge_prop_impl              false
% 6.99/1.49  --prep_def_merge_mbd                    true
% 6.99/1.49  --prep_def_merge_tr_red                 false
% 6.99/1.49  --prep_def_merge_tr_cl                  false
% 6.99/1.49  --smt_preprocessing                     true
% 6.99/1.49  --smt_ac_axioms                         fast
% 6.99/1.49  --preprocessed_out                      false
% 6.99/1.49  --preprocessed_stats                    false
% 6.99/1.49  
% 6.99/1.49  ------ Abstraction refinement Options
% 6.99/1.49  
% 6.99/1.49  --abstr_ref                             []
% 6.99/1.49  --abstr_ref_prep                        false
% 6.99/1.49  --abstr_ref_until_sat                   false
% 6.99/1.49  --abstr_ref_sig_restrict                funpre
% 6.99/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.49  --abstr_ref_under                       []
% 6.99/1.49  
% 6.99/1.49  ------ SAT Options
% 6.99/1.49  
% 6.99/1.49  --sat_mode                              false
% 6.99/1.49  --sat_fm_restart_options                ""
% 6.99/1.49  --sat_gr_def                            false
% 6.99/1.49  --sat_epr_types                         true
% 6.99/1.49  --sat_non_cyclic_types                  false
% 6.99/1.49  --sat_finite_models                     false
% 6.99/1.49  --sat_fm_lemmas                         false
% 6.99/1.49  --sat_fm_prep                           false
% 6.99/1.49  --sat_fm_uc_incr                        true
% 6.99/1.49  --sat_out_model                         small
% 6.99/1.49  --sat_out_clauses                       false
% 6.99/1.49  
% 6.99/1.49  ------ QBF Options
% 6.99/1.49  
% 6.99/1.49  --qbf_mode                              false
% 6.99/1.49  --qbf_elim_univ                         false
% 6.99/1.49  --qbf_dom_inst                          none
% 6.99/1.49  --qbf_dom_pre_inst                      false
% 6.99/1.49  --qbf_sk_in                             false
% 6.99/1.49  --qbf_pred_elim                         true
% 6.99/1.49  --qbf_split                             512
% 6.99/1.49  
% 6.99/1.49  ------ BMC1 Options
% 6.99/1.49  
% 6.99/1.49  --bmc1_incremental                      false
% 6.99/1.49  --bmc1_axioms                           reachable_all
% 6.99/1.49  --bmc1_min_bound                        0
% 6.99/1.49  --bmc1_max_bound                        -1
% 6.99/1.49  --bmc1_max_bound_default                -1
% 6.99/1.49  --bmc1_symbol_reachability              true
% 6.99/1.49  --bmc1_property_lemmas                  false
% 6.99/1.49  --bmc1_k_induction                      false
% 6.99/1.49  --bmc1_non_equiv_states                 false
% 6.99/1.49  --bmc1_deadlock                         false
% 6.99/1.49  --bmc1_ucm                              false
% 6.99/1.49  --bmc1_add_unsat_core                   none
% 6.99/1.49  --bmc1_unsat_core_children              false
% 6.99/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.49  --bmc1_out_stat                         full
% 6.99/1.49  --bmc1_ground_init                      false
% 6.99/1.49  --bmc1_pre_inst_next_state              false
% 6.99/1.49  --bmc1_pre_inst_state                   false
% 6.99/1.49  --bmc1_pre_inst_reach_state             false
% 6.99/1.49  --bmc1_out_unsat_core                   false
% 6.99/1.49  --bmc1_aig_witness_out                  false
% 6.99/1.49  --bmc1_verbose                          false
% 6.99/1.49  --bmc1_dump_clauses_tptp                false
% 6.99/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.49  --bmc1_dump_file                        -
% 6.99/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.49  --bmc1_ucm_extend_mode                  1
% 6.99/1.49  --bmc1_ucm_init_mode                    2
% 6.99/1.49  --bmc1_ucm_cone_mode                    none
% 6.99/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.49  --bmc1_ucm_relax_model                  4
% 6.99/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.49  --bmc1_ucm_layered_model                none
% 6.99/1.49  --bmc1_ucm_max_lemma_size               10
% 6.99/1.49  
% 6.99/1.49  ------ AIG Options
% 6.99/1.49  
% 6.99/1.49  --aig_mode                              false
% 6.99/1.49  
% 6.99/1.49  ------ Instantiation Options
% 6.99/1.49  
% 6.99/1.49  --instantiation_flag                    true
% 6.99/1.49  --inst_sos_flag                         false
% 6.99/1.49  --inst_sos_phase                        true
% 6.99/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.49  --inst_lit_sel_side                     none
% 6.99/1.49  --inst_solver_per_active                1400
% 6.99/1.49  --inst_solver_calls_frac                1.
% 6.99/1.49  --inst_passive_queue_type               priority_queues
% 6.99/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.49  --inst_passive_queues_freq              [25;2]
% 6.99/1.49  --inst_dismatching                      true
% 6.99/1.49  --inst_eager_unprocessed_to_passive     true
% 6.99/1.49  --inst_prop_sim_given                   true
% 6.99/1.49  --inst_prop_sim_new                     false
% 6.99/1.49  --inst_subs_new                         false
% 6.99/1.49  --inst_eq_res_simp                      false
% 6.99/1.49  --inst_subs_given                       false
% 6.99/1.49  --inst_orphan_elimination               true
% 6.99/1.49  --inst_learning_loop_flag               true
% 6.99/1.49  --inst_learning_start                   3000
% 6.99/1.49  --inst_learning_factor                  2
% 6.99/1.49  --inst_start_prop_sim_after_learn       3
% 6.99/1.49  --inst_sel_renew                        solver
% 6.99/1.49  --inst_lit_activity_flag                true
% 6.99/1.49  --inst_restr_to_given                   false
% 6.99/1.49  --inst_activity_threshold               500
% 6.99/1.49  --inst_out_proof                        true
% 6.99/1.49  
% 6.99/1.49  ------ Resolution Options
% 6.99/1.49  
% 6.99/1.49  --resolution_flag                       false
% 6.99/1.49  --res_lit_sel                           adaptive
% 6.99/1.49  --res_lit_sel_side                      none
% 6.99/1.49  --res_ordering                          kbo
% 6.99/1.49  --res_to_prop_solver                    active
% 6.99/1.49  --res_prop_simpl_new                    false
% 6.99/1.49  --res_prop_simpl_given                  true
% 6.99/1.49  --res_passive_queue_type                priority_queues
% 6.99/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.49  --res_passive_queues_freq               [15;5]
% 6.99/1.49  --res_forward_subs                      full
% 6.99/1.49  --res_backward_subs                     full
% 6.99/1.49  --res_forward_subs_resolution           true
% 6.99/1.49  --res_backward_subs_resolution          true
% 6.99/1.49  --res_orphan_elimination                true
% 6.99/1.49  --res_time_limit                        2.
% 6.99/1.49  --res_out_proof                         true
% 6.99/1.49  
% 6.99/1.49  ------ Superposition Options
% 6.99/1.49  
% 6.99/1.49  --superposition_flag                    true
% 6.99/1.49  --sup_passive_queue_type                priority_queues
% 6.99/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.49  --demod_completeness_check              fast
% 6.99/1.49  --demod_use_ground                      true
% 6.99/1.49  --sup_to_prop_solver                    passive
% 6.99/1.49  --sup_prop_simpl_new                    true
% 6.99/1.49  --sup_prop_simpl_given                  true
% 6.99/1.49  --sup_fun_splitting                     false
% 6.99/1.49  --sup_smt_interval                      50000
% 6.99/1.49  
% 6.99/1.49  ------ Superposition Simplification Setup
% 6.99/1.49  
% 6.99/1.49  --sup_indices_passive                   []
% 6.99/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_full_bw                           [BwDemod]
% 6.99/1.49  --sup_immed_triv                        [TrivRules]
% 6.99/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_immed_bw_main                     []
% 6.99/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.49  
% 6.99/1.49  ------ Combination Options
% 6.99/1.49  
% 6.99/1.49  --comb_res_mult                         3
% 6.99/1.49  --comb_sup_mult                         2
% 6.99/1.49  --comb_inst_mult                        10
% 6.99/1.49  
% 6.99/1.49  ------ Debug Options
% 6.99/1.49  
% 6.99/1.49  --dbg_backtrace                         false
% 6.99/1.49  --dbg_dump_prop_clauses                 false
% 6.99/1.49  --dbg_dump_prop_clauses_file            -
% 6.99/1.49  --dbg_out_stat                          false
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  ------ Proving...
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  % SZS status Theorem for theBenchmark.p
% 6.99/1.49  
% 6.99/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.99/1.49  
% 6.99/1.49  fof(f15,axiom,(
% 6.99/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f33,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(ennf_transformation,[],[f15])).
% 6.99/1.49  
% 6.99/1.49  fof(f34,plain,(
% 6.99/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(flattening,[],[f33])).
% 6.99/1.49  
% 6.99/1.49  fof(f51,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(nnf_transformation,[],[f34])).
% 6.99/1.49  
% 6.99/1.49  fof(f80,plain,(
% 6.99/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(cnf_transformation,[],[f51])).
% 6.99/1.49  
% 6.99/1.49  fof(f16,conjecture,(
% 6.99/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f17,negated_conjecture,(
% 6.99/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 6.99/1.49    inference(negated_conjecture,[],[f16])).
% 6.99/1.49  
% 6.99/1.49  fof(f35,plain,(
% 6.99/1.49    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 6.99/1.49    inference(ennf_transformation,[],[f17])).
% 6.99/1.49  
% 6.99/1.49  fof(f36,plain,(
% 6.99/1.49    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 6.99/1.49    inference(flattening,[],[f35])).
% 6.99/1.49  
% 6.99/1.49  fof(f53,plain,(
% 6.99/1.49    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK7) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK7,X0,X1) & v1_funct_1(sK7))) )),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f52,plain,(
% 6.99/1.49    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK4,sK5,sK6,X3) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f54,plain,(
% 6.99/1.49    (~r2_relset_1(sK4,sK5,sK6,sK7) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~m1_subset_1(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 6.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f36,f53,f52])).
% 6.99/1.49  
% 6.99/1.49  fof(f90,plain,(
% 6.99/1.49    v1_funct_2(sK7,sK4,sK5)),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f91,plain,(
% 6.99/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f13,axiom,(
% 6.99/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f30,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(ennf_transformation,[],[f13])).
% 6.99/1.49  
% 6.99/1.49  fof(f77,plain,(
% 6.99/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(cnf_transformation,[],[f30])).
% 6.99/1.49  
% 6.99/1.49  fof(f87,plain,(
% 6.99/1.49    v1_funct_2(sK6,sK4,sK5)),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f88,plain,(
% 6.99/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f9,axiom,(
% 6.99/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f25,plain,(
% 6.99/1.49    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.99/1.49    inference(ennf_transformation,[],[f9])).
% 6.99/1.49  
% 6.99/1.49  fof(f26,plain,(
% 6.99/1.49    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.99/1.49    inference(flattening,[],[f25])).
% 6.99/1.49  
% 6.99/1.49  fof(f42,plain,(
% 6.99/1.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f43,plain,(
% 6.99/1.49    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f42])).
% 6.99/1.49  
% 6.99/1.49  fof(f67,plain,(
% 6.99/1.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f43])).
% 6.99/1.49  
% 6.99/1.49  fof(f89,plain,(
% 6.99/1.49    v1_funct_1(sK7)),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f2,axiom,(
% 6.99/1.49    v1_xboole_0(k1_xboole_0)),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f57,plain,(
% 6.99/1.49    v1_xboole_0(k1_xboole_0)),
% 6.99/1.49    inference(cnf_transformation,[],[f2])).
% 6.99/1.49  
% 6.99/1.49  fof(f10,axiom,(
% 6.99/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f27,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(ennf_transformation,[],[f10])).
% 6.99/1.49  
% 6.99/1.49  fof(f69,plain,(
% 6.99/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(cnf_transformation,[],[f27])).
% 6.99/1.49  
% 6.99/1.49  fof(f11,axiom,(
% 6.99/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f28,plain,(
% 6.99/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 6.99/1.49    inference(ennf_transformation,[],[f11])).
% 6.99/1.49  
% 6.99/1.49  fof(f70,plain,(
% 6.99/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f28])).
% 6.99/1.49  
% 6.99/1.49  fof(f12,axiom,(
% 6.99/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f29,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(ennf_transformation,[],[f12])).
% 6.99/1.49  
% 6.99/1.49  fof(f44,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(nnf_transformation,[],[f29])).
% 6.99/1.49  
% 6.99/1.49  fof(f45,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(flattening,[],[f44])).
% 6.99/1.49  
% 6.99/1.49  fof(f46,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(rectify,[],[f45])).
% 6.99/1.49  
% 6.99/1.49  fof(f48,plain,(
% 6.99/1.49    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2)) & m1_subset_1(sK3(X0,X1,X2,X3),X1)))) )),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f47,plain,(
% 6.99/1.49    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK2(X0,X1,X2,X3),X0)))),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f49,plain,(
% 6.99/1.49    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)) & m1_subset_1(sK3(X0,X1,X2,X3),X1)) & m1_subset_1(sK2(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).
% 6.99/1.49  
% 6.99/1.49  fof(f75,plain,(
% 6.99/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(cnf_transformation,[],[f49])).
% 6.99/1.49  
% 6.99/1.49  fof(f93,plain,(
% 6.99/1.49    ~r2_relset_1(sK4,sK5,sK6,sK7)),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f1,axiom,(
% 6.99/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f37,plain,(
% 6.99/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.99/1.49    inference(nnf_transformation,[],[f1])).
% 6.99/1.49  
% 6.99/1.49  fof(f38,plain,(
% 6.99/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.99/1.49    inference(rectify,[],[f37])).
% 6.99/1.49  
% 6.99/1.49  fof(f39,plain,(
% 6.99/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.99/1.49    introduced(choice_axiom,[])).
% 6.99/1.49  
% 6.99/1.49  fof(f40,plain,(
% 6.99/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 6.99/1.49  
% 6.99/1.49  fof(f55,plain,(
% 6.99/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f40])).
% 6.99/1.49  
% 6.99/1.49  fof(f86,plain,(
% 6.99/1.49    v1_funct_1(sK6)),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f14,axiom,(
% 6.99/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f31,plain,(
% 6.99/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.99/1.49    inference(ennf_transformation,[],[f14])).
% 6.99/1.49  
% 6.99/1.49  fof(f32,plain,(
% 6.99/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(flattening,[],[f31])).
% 6.99/1.49  
% 6.99/1.49  fof(f50,plain,(
% 6.99/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.49    inference(nnf_transformation,[],[f32])).
% 6.99/1.49  
% 6.99/1.49  fof(f79,plain,(
% 6.99/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(cnf_transformation,[],[f50])).
% 6.99/1.49  
% 6.99/1.49  fof(f94,plain,(
% 6.99/1.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.49    inference(equality_resolution,[],[f79])).
% 6.99/1.49  
% 6.99/1.49  fof(f4,axiom,(
% 6.99/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.49  
% 6.99/1.49  fof(f20,plain,(
% 6.99/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.99/1.49    inference(ennf_transformation,[],[f4])).
% 6.99/1.49  
% 6.99/1.49  fof(f41,plain,(
% 6.99/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 6.99/1.49    inference(nnf_transformation,[],[f20])).
% 6.99/1.49  
% 6.99/1.49  fof(f60,plain,(
% 6.99/1.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f41])).
% 6.99/1.49  
% 6.99/1.49  fof(f92,plain,(
% 6.99/1.49    ( ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~m1_subset_1(X4,sK4)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f54])).
% 6.99/1.49  
% 6.99/1.49  fof(f68,plain,(
% 6.99/1.49    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.99/1.49    inference(cnf_transformation,[],[f43])).
% 6.99/1.49  
% 6.99/1.49  cnf(c_30,plain,
% 6.99/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | k1_relset_1(X1,X2,X0) = X1
% 6.99/1.49      | k1_xboole_0 = X2 ),
% 6.99/1.49      inference(cnf_transformation,[],[f80]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_34,negated_conjecture,
% 6.99/1.49      ( v1_funct_2(sK7,sK4,sK5) ),
% 6.99/1.49      inference(cnf_transformation,[],[f90]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_514,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | k1_relset_1(X1,X2,X0) = X1
% 6.99/1.49      | sK7 != X0
% 6.99/1.49      | sK5 != X2
% 6.99/1.49      | sK4 != X1
% 6.99/1.49      | k1_xboole_0 = X2 ),
% 6.99/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_515,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | k1_relset_1(sK4,sK5,sK7) = sK4
% 6.99/1.49      | k1_xboole_0 = sK5 ),
% 6.99/1.49      inference(unflattening,[status(thm)],[c_514]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_33,negated_conjecture,
% 6.99/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 6.99/1.49      inference(cnf_transformation,[],[f91]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_517,plain,
% 6.99/1.49      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_515,c_33]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2220,plain,
% 6.99/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_22,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f77]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2225,plain,
% 6.99/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.99/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3289,plain,
% 6.99/1.49      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_2220,c_2225]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3514,plain,
% 6.99/1.49      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_517,c_3289]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_37,negated_conjecture,
% 6.99/1.49      ( v1_funct_2(sK6,sK4,sK5) ),
% 6.99/1.49      inference(cnf_transformation,[],[f87]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_525,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | k1_relset_1(X1,X2,X0) = X1
% 6.99/1.49      | sK6 != X0
% 6.99/1.49      | sK5 != X2
% 6.99/1.49      | sK4 != X1
% 6.99/1.49      | k1_xboole_0 = X2 ),
% 6.99/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_526,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | k1_relset_1(sK4,sK5,sK6) = sK4
% 6.99/1.49      | k1_xboole_0 = sK5 ),
% 6.99/1.49      inference(unflattening,[status(thm)],[c_525]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_36,negated_conjecture,
% 6.99/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 6.99/1.49      inference(cnf_transformation,[],[f88]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_528,plain,
% 6.99/1.49      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_526,c_36]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2218,plain,
% 6.99/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3290,plain,
% 6.99/1.49      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_2218,c_2225]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3517,plain,
% 6.99/1.49      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_528,c_3290]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13,plain,
% 6.99/1.49      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 6.99/1.49      | ~ v1_relat_1(X1)
% 6.99/1.49      | ~ v1_relat_1(X0)
% 6.99/1.49      | ~ v1_funct_1(X1)
% 6.99/1.49      | ~ v1_funct_1(X0)
% 6.99/1.49      | X1 = X0
% 6.99/1.49      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2234,plain,
% 6.99/1.49      ( X0 = X1
% 6.99/1.49      | k1_relat_1(X0) != k1_relat_1(X1)
% 6.99/1.49      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 6.99/1.49      | v1_relat_1(X1) != iProver_top
% 6.99/1.49      | v1_relat_1(X0) != iProver_top
% 6.99/1.49      | v1_funct_1(X0) != iProver_top
% 6.99/1.49      | v1_funct_1(X1) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_5710,plain,
% 6.99/1.49      ( k1_relat_1(X0) != sK4
% 6.99/1.49      | sK7 = X0
% 6.99/1.49      | sK5 = k1_xboole_0
% 6.99/1.49      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 6.99/1.49      | v1_relat_1(X0) != iProver_top
% 6.99/1.49      | v1_relat_1(sK7) != iProver_top
% 6.99/1.49      | v1_funct_1(X0) != iProver_top
% 6.99/1.49      | v1_funct_1(sK7) != iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_3514,c_2234]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_35,negated_conjecture,
% 6.99/1.49      ( v1_funct_1(sK7) ),
% 6.99/1.49      inference(cnf_transformation,[],[f89]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_42,plain,
% 6.99/1.49      ( v1_funct_1(sK7) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_44,plain,
% 6.99/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2,plain,
% 6.99/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_14,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | v1_relat_1(X0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2558,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | v1_relat_1(sK7) ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2559,plain,
% 6.99/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 6.99/1.49      | v1_relat_1(sK7) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2558]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_15,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | ~ v1_xboole_0(X2)
% 6.99/1.49      | v1_xboole_0(X0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2232,plain,
% 6.99/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.99/1.49      | v1_xboole_0(X2) != iProver_top
% 6.99/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3783,plain,
% 6.99/1.49      ( v1_xboole_0(sK7) = iProver_top
% 6.99/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_2220,c_2232]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_17,plain,
% 6.99/1.49      ( r2_relset_1(X0,X1,X2,X3)
% 6.99/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.99/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
% 6.99/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_31,negated_conjecture,
% 6.99/1.49      ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
% 6.99/1.49      inference(cnf_transformation,[],[f93]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_864,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(X1,X2,X0,X3),sK3(X1,X2,X0,X3)),X3)
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(X1,X2,X0,X3),sK3(X1,X2,X0,X3)),X0)
% 6.99/1.49      | sK7 != X3
% 6.99/1.49      | sK6 != X0
% 6.99/1.49      | sK5 != X2
% 6.99/1.49      | sK4 != X1 ),
% 6.99/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_31]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_865,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
% 6.99/1.49      inference(unflattening,[status(thm)],[c_864]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_867,plain,
% 6.99/1.49      ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_865,c_36,c_33]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_869,plain,
% 6.99/1.49      ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 6.99/1.49      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_1,plain,
% 6.99/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.99/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3340,plain,
% 6.99/1.49      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 6.99/1.49      | ~ v1_xboole_0(sK7) ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3341,plain,
% 6.99/1.49      ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) != iProver_top
% 6.99/1.49      | v1_xboole_0(sK7) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_3340]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3565,plain,
% 6.99/1.49      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6)
% 6.99/1.49      | ~ v1_xboole_0(sK6) ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3566,plain,
% 6.99/1.49      ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) != iProver_top
% 6.99/1.49      | v1_xboole_0(sK6) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_3565]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3784,plain,
% 6.99/1.49      ( v1_xboole_0(sK6) = iProver_top
% 6.99/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_2218,c_2232]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3984,plain,
% 6.99/1.49      ( v1_xboole_0(sK5) != iProver_top ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_3783,c_869,c_3341,c_3566,c_3784]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3986,plain,
% 6.99/1.49      ( ~ v1_xboole_0(sK5) ),
% 6.99/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3984]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_1632,plain,
% 6.99/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.99/1.49      theory(equality) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_7948,plain,
% 6.99/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_1632]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_7950,plain,
% 6.99/1.49      ( v1_xboole_0(sK5)
% 6.99/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 6.99/1.49      | sK5 != k1_xboole_0 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_7948]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13575,plain,
% 6.99/1.49      ( v1_funct_1(X0) != iProver_top
% 6.99/1.49      | sK7 = X0
% 6.99/1.49      | k1_relat_1(X0) != sK4
% 6.99/1.49      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 6.99/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_5710,c_42,c_44,c_2,c_2559,c_3986,c_7950]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13576,plain,
% 6.99/1.49      ( k1_relat_1(X0) != sK4
% 6.99/1.49      | sK7 = X0
% 6.99/1.49      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 6.99/1.49      | v1_relat_1(X0) != iProver_top
% 6.99/1.49      | v1_funct_1(X0) != iProver_top ),
% 6.99/1.49      inference(renaming,[status(thm)],[c_13575]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13587,plain,
% 6.99/1.49      ( sK7 = sK6
% 6.99/1.49      | sK5 = k1_xboole_0
% 6.99/1.49      | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
% 6.99/1.49      | v1_relat_1(sK6) != iProver_top
% 6.99/1.49      | v1_funct_1(sK6) != iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_3517,c_13576]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_38,negated_conjecture,
% 6.99/1.49      ( v1_funct_1(sK6) ),
% 6.99/1.49      inference(cnf_transformation,[],[f86]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_39,plain,
% 6.99/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_41,plain,
% 6.99/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_23,plain,
% 6.99/1.49      ( r2_relset_1(X0,X1,X2,X2)
% 6.99/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.99/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_892,plain,
% 6.99/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.49      | sK7 != X0
% 6.99/1.49      | sK6 != X0
% 6.99/1.49      | sK5 != X2
% 6.99/1.49      | sK4 != X1 ),
% 6.99/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_893,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | sK6 != sK7 ),
% 6.99/1.49      inference(unflattening,[status(thm)],[c_892]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2561,plain,
% 6.99/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.99/1.49      | v1_relat_1(sK6) ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2562,plain,
% 6.99/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 6.99/1.49      | v1_relat_1(sK6) = iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2561]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_1630,plain,( X0 = X0 ),theory(equality) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_4280,plain,
% 6.99/1.49      ( sK6 = sK6 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_1630]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_1631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2757,plain,
% 6.99/1.49      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_1631]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_3378,plain,
% 6.99/1.49      ( X0 = sK7 | X0 != sK6 | sK7 != sK6 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_2757]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_4285,plain,
% 6.99/1.49      ( sK7 != sK6 | sK6 = sK7 | sK6 != sK6 ),
% 6.99/1.49      inference(instantiation,[status(thm)],[c_3378]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13600,plain,
% 6.99/1.49      ( r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_13587,c_39,c_41,c_33,c_2,c_893,c_2562,c_3986,c_4280,
% 6.99/1.49                 c_4285,c_7950]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13605,plain,
% 6.99/1.49      ( sK5 = k1_xboole_0 | r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_3517,c_13600]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13730,plain,
% 6.99/1.49      ( r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_13605,c_2,c_3986,c_7950]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_6,plain,
% 6.99/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.99/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_233,plain,
% 6.99/1.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 6.99/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6,c_1]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_234,plain,
% 6.99/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 6.99/1.49      inference(renaming,[status(thm)],[c_233]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2216,plain,
% 6.99/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 6.99/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_13735,plain,
% 6.99/1.49      ( m1_subset_1(sK1(sK6,sK7),sK4) = iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_13730,c_2216]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_32,negated_conjecture,
% 6.99/1.49      ( ~ m1_subset_1(X0,sK4) | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
% 6.99/1.49      inference(cnf_transformation,[],[f92]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2221,plain,
% 6.99/1.49      ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
% 6.99/1.49      | m1_subset_1(X0,sK4) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_23740,plain,
% 6.99/1.49      ( k1_funct_1(sK6,sK1(sK6,sK7)) = k1_funct_1(sK7,sK1(sK6,sK7)) ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_13735,c_2221]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_12,plain,
% 6.99/1.49      ( ~ v1_relat_1(X0)
% 6.99/1.49      | ~ v1_relat_1(X1)
% 6.99/1.49      | ~ v1_funct_1(X0)
% 6.99/1.49      | ~ v1_funct_1(X1)
% 6.99/1.49      | X0 = X1
% 6.99/1.49      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 6.99/1.49      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 6.99/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_2235,plain,
% 6.99/1.49      ( X0 = X1
% 6.99/1.49      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 6.99/1.49      | k1_relat_1(X0) != k1_relat_1(X1)
% 6.99/1.49      | v1_relat_1(X0) != iProver_top
% 6.99/1.49      | v1_relat_1(X1) != iProver_top
% 6.99/1.49      | v1_funct_1(X1) != iProver_top
% 6.99/1.49      | v1_funct_1(X0) != iProver_top ),
% 6.99/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_23852,plain,
% 6.99/1.49      ( k1_relat_1(sK6) != k1_relat_1(sK7)
% 6.99/1.49      | sK7 = sK6
% 6.99/1.49      | v1_relat_1(sK7) != iProver_top
% 6.99/1.49      | v1_relat_1(sK6) != iProver_top
% 6.99/1.49      | v1_funct_1(sK7) != iProver_top
% 6.99/1.49      | v1_funct_1(sK6) != iProver_top ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_23740,c_2235]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_23855,plain,
% 6.99/1.49      ( k1_relat_1(sK6) != k1_relat_1(sK7) ),
% 6.99/1.49      inference(global_propositional_subsumption,
% 6.99/1.49                [status(thm)],
% 6.99/1.49                [c_23852,c_39,c_41,c_42,c_33,c_44,c_893,c_2559,c_2562,
% 6.99/1.49                 c_4280,c_4285]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(c_23858,plain,
% 6.99/1.49      ( k1_relat_1(sK6) != sK4 | sK5 = k1_xboole_0 ),
% 6.99/1.49      inference(superposition,[status(thm)],[c_3514,c_23855]) ).
% 6.99/1.49  
% 6.99/1.49  cnf(contradiction,plain,
% 6.99/1.49      ( $false ),
% 6.99/1.49      inference(minisat,[status(thm)],[c_23858,c_7950,c_3986,c_3517,c_2]) ).
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.99/1.49  
% 6.99/1.49  ------                               Statistics
% 6.99/1.49  
% 6.99/1.49  ------ General
% 6.99/1.49  
% 6.99/1.49  abstr_ref_over_cycles:                  0
% 6.99/1.49  abstr_ref_under_cycles:                 0
% 6.99/1.49  gc_basic_clause_elim:                   0
% 6.99/1.49  forced_gc_time:                         0
% 6.99/1.49  parsing_time:                           0.009
% 6.99/1.49  unif_index_cands_time:                  0.
% 6.99/1.49  unif_index_add_time:                    0.
% 6.99/1.49  orderings_time:                         0.
% 6.99/1.49  out_proof_time:                         0.023
% 6.99/1.49  total_time:                             0.617
% 6.99/1.49  num_of_symbols:                         54
% 6.99/1.49  num_of_terms:                           17407
% 6.99/1.49  
% 6.99/1.49  ------ Preprocessing
% 6.99/1.49  
% 6.99/1.49  num_of_splits:                          0
% 6.99/1.49  num_of_split_atoms:                     0
% 6.99/1.49  num_of_reused_defs:                     0
% 6.99/1.49  num_eq_ax_congr_red:                    42
% 6.99/1.49  num_of_sem_filtered_clauses:            1
% 6.99/1.49  num_of_subtypes:                        0
% 6.99/1.49  monotx_restored_types:                  0
% 6.99/1.49  sat_num_of_epr_types:                   0
% 6.99/1.49  sat_num_of_non_cyclic_types:            0
% 6.99/1.49  sat_guarded_non_collapsed_types:        0
% 6.99/1.49  num_pure_diseq_elim:                    0
% 6.99/1.49  simp_replaced_by:                       0
% 6.99/1.49  res_preprocessed:                       172
% 6.99/1.49  prep_upred:                             0
% 6.99/1.49  prep_unflattend:                        98
% 6.99/1.49  smt_new_axioms:                         0
% 6.99/1.49  pred_elim_cands:                        6
% 6.99/1.49  pred_elim:                              2
% 6.99/1.49  pred_elim_cl:                           3
% 6.99/1.49  pred_elim_cycles:                       4
% 6.99/1.49  merged_defs:                            0
% 6.99/1.49  merged_defs_ncl:                        0
% 6.99/1.49  bin_hyper_res:                          0
% 6.99/1.49  prep_cycles:                            4
% 6.99/1.49  pred_elim_time:                         0.019
% 6.99/1.49  splitting_time:                         0.
% 6.99/1.49  sem_filter_time:                        0.
% 6.99/1.49  monotx_time:                            0.
% 6.99/1.49  subtype_inf_time:                       0.
% 6.99/1.49  
% 6.99/1.49  ------ Problem properties
% 6.99/1.49  
% 6.99/1.49  clauses:                                36
% 6.99/1.49  conjectures:                            6
% 6.99/1.49  epr:                                    9
% 6.99/1.49  horn:                                   26
% 6.99/1.49  ground:                                 12
% 6.99/1.49  unary:                                  7
% 6.99/1.49  binary:                                 10
% 6.99/1.49  lits:                                   109
% 6.99/1.49  lits_eq:                                23
% 6.99/1.49  fd_pure:                                0
% 6.99/1.49  fd_pseudo:                              0
% 6.99/1.49  fd_cond:                                1
% 6.99/1.49  fd_pseudo_cond:                         3
% 6.99/1.49  ac_symbols:                             0
% 6.99/1.49  
% 6.99/1.49  ------ Propositional Solver
% 6.99/1.49  
% 6.99/1.49  prop_solver_calls:                      32
% 6.99/1.49  prop_fast_solver_calls:                 2320
% 6.99/1.49  smt_solver_calls:                       0
% 6.99/1.49  smt_fast_solver_calls:                  0
% 6.99/1.49  prop_num_of_clauses:                    7197
% 6.99/1.49  prop_preprocess_simplified:             12722
% 6.99/1.49  prop_fo_subsumed:                       83
% 6.99/1.49  prop_solver_time:                       0.
% 6.99/1.49  smt_solver_time:                        0.
% 6.99/1.49  smt_fast_solver_time:                   0.
% 6.99/1.49  prop_fast_solver_time:                  0.
% 6.99/1.49  prop_unsat_core_time:                   0.
% 6.99/1.49  
% 6.99/1.49  ------ QBF
% 6.99/1.49  
% 6.99/1.49  qbf_q_res:                              0
% 6.99/1.49  qbf_num_tautologies:                    0
% 6.99/1.49  qbf_prep_cycles:                        0
% 6.99/1.49  
% 6.99/1.49  ------ BMC1
% 6.99/1.49  
% 6.99/1.49  bmc1_current_bound:                     -1
% 6.99/1.49  bmc1_last_solved_bound:                 -1
% 6.99/1.49  bmc1_unsat_core_size:                   -1
% 6.99/1.49  bmc1_unsat_core_parents_size:           -1
% 6.99/1.49  bmc1_merge_next_fun:                    0
% 6.99/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.99/1.49  
% 6.99/1.49  ------ Instantiation
% 6.99/1.49  
% 6.99/1.49  inst_num_of_clauses:                    1859
% 6.99/1.49  inst_num_in_passive:                    781
% 6.99/1.49  inst_num_in_active:                     880
% 6.99/1.49  inst_num_in_unprocessed:                198
% 6.99/1.49  inst_num_of_loops:                      1210
% 6.99/1.49  inst_num_of_learning_restarts:          0
% 6.99/1.49  inst_num_moves_active_passive:          325
% 6.99/1.49  inst_lit_activity:                      0
% 6.99/1.49  inst_lit_activity_moves:                0
% 6.99/1.49  inst_num_tautologies:                   0
% 6.99/1.49  inst_num_prop_implied:                  0
% 6.99/1.49  inst_num_existing_simplified:           0
% 6.99/1.49  inst_num_eq_res_simplified:             0
% 6.99/1.49  inst_num_child_elim:                    0
% 6.99/1.49  inst_num_of_dismatching_blockings:      973
% 6.99/1.49  inst_num_of_non_proper_insts:           3026
% 6.99/1.49  inst_num_of_duplicates:                 0
% 6.99/1.49  inst_inst_num_from_inst_to_res:         0
% 6.99/1.49  inst_dismatching_checking_time:         0.
% 6.99/1.49  
% 6.99/1.49  ------ Resolution
% 6.99/1.49  
% 6.99/1.49  res_num_of_clauses:                     0
% 6.99/1.49  res_num_in_passive:                     0
% 6.99/1.49  res_num_in_active:                      0
% 6.99/1.49  res_num_of_loops:                       176
% 6.99/1.49  res_forward_subset_subsumed:            141
% 6.99/1.49  res_backward_subset_subsumed:           0
% 6.99/1.49  res_forward_subsumed:                   0
% 6.99/1.49  res_backward_subsumed:                  0
% 6.99/1.49  res_forward_subsumption_resolution:     0
% 6.99/1.49  res_backward_subsumption_resolution:    0
% 6.99/1.49  res_clause_to_clause_subsumption:       3518
% 6.99/1.49  res_orphan_elimination:                 0
% 6.99/1.49  res_tautology_del:                      148
% 6.99/1.49  res_num_eq_res_simplified:              0
% 6.99/1.49  res_num_sel_changes:                    0
% 6.99/1.49  res_moves_from_active_to_pass:          0
% 6.99/1.49  
% 6.99/1.49  ------ Superposition
% 6.99/1.49  
% 6.99/1.49  sup_time_total:                         0.
% 6.99/1.49  sup_time_generating:                    0.
% 6.99/1.49  sup_time_sim_full:                      0.
% 6.99/1.49  sup_time_sim_immed:                     0.
% 6.99/1.49  
% 6.99/1.49  sup_num_of_clauses:                     509
% 6.99/1.49  sup_num_in_active:                      239
% 6.99/1.49  sup_num_in_passive:                     270
% 6.99/1.49  sup_num_of_loops:                       241
% 6.99/1.49  sup_fw_superposition:                   384
% 6.99/1.49  sup_bw_superposition:                   244
% 6.99/1.49  sup_immediate_simplified:               106
% 6.99/1.49  sup_given_eliminated:                   0
% 6.99/1.49  comparisons_done:                       0
% 6.99/1.49  comparisons_avoided:                    52
% 6.99/1.49  
% 6.99/1.49  ------ Simplifications
% 6.99/1.49  
% 6.99/1.49  
% 6.99/1.49  sim_fw_subset_subsumed:                 82
% 6.99/1.49  sim_bw_subset_subsumed:                 4
% 6.99/1.49  sim_fw_subsumed:                        23
% 6.99/1.49  sim_bw_subsumed:                        1
% 6.99/1.49  sim_fw_subsumption_res:                 1
% 6.99/1.49  sim_bw_subsumption_res:                 0
% 6.99/1.49  sim_tautology_del:                      19
% 6.99/1.49  sim_eq_tautology_del:                   11
% 6.99/1.49  sim_eq_res_simp:                        1
% 6.99/1.49  sim_fw_demodulated:                     0
% 6.99/1.49  sim_bw_demodulated:                     0
% 6.99/1.49  sim_light_normalised:                   0
% 6.99/1.49  sim_joinable_taut:                      0
% 6.99/1.49  sim_joinable_simp:                      0
% 6.99/1.49  sim_ac_normalised:                      0
% 6.99/1.49  sim_smt_subsumption:                    0
% 6.99/1.49  
%------------------------------------------------------------------------------
