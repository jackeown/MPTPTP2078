%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:13 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  138 (1347 expanded)
%              Number of clauses        :   82 ( 389 expanded)
%              Number of leaves         :   16 ( 338 expanded)
%              Depth                    :   26
%              Number of atoms          :  566 (9254 expanded)
%              Number of equality atoms :  213 (2067 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
     => ( ~ r2_relset_1(X0,X1,X2,sK7)
        & ! [X4] :
            ( k1_funct_1(sK7,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7,X0,X1)
        & v1_funct_1(sK7) ) ) ),
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
          ( ~ r2_relset_1(sK4,sK5,sK6,X3)
          & ! [X4] :
              ( k1_funct_1(sK6,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7)
    & ! [X4] :
        ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
        | ~ r2_hidden(X4,sK4) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f44,f43])).

fof(f75,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
      | ~ r2_hidden(X4,sK4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8041,plain,
    ( r1_tarski(k1_xboole_0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_442,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_33])).

cnf(c_1798,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1803,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2205,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1798,c_1803])).

cnf(c_2478,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_2205])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_429,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_431,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_30])).

cnf(c_1800,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2204,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1800,c_1803])).

cnf(c_2425,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_431,c_2204])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1812,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4675,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2425,c_1812])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2084,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2085,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_5714,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4675,c_39,c_41,c_2085])).

cnf(c_5715,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5714])).

cnf(c_5727,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_5715])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2087,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2088,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_5865,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5727,c_36,c_38,c_2088])).

cnf(c_5872,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_5865])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1801,plain,
    ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5906,plain,
    ( k1_funct_1(sK6,sK1(sK6,sK7)) = k1_funct_1(sK7,sK1(sK6,sK7))
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5872,c_1801])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1813,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6534,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5906,c_1813])).

cnf(c_1301,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2842,plain,
    ( k1_relat_1(sK7) != X0
    | k1_relat_1(sK6) != X0
    | k1_relat_1(sK6) = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_6382,plain,
    ( k1_relat_1(sK7) != sK4
    | k1_relat_1(sK6) = k1_relat_1(sK7)
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_6535,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6534])).

cnf(c_6739,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6534,c_35,c_33,c_32,c_30,c_2084,c_2087,c_2425,c_2478,c_6382,c_6535])).

cnf(c_28,negated_conjecture,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1802,plain,
    ( r2_relset_1(sK4,sK5,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6755,plain,
    ( sK5 = k1_xboole_0
    | r2_relset_1(sK4,sK5,sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6739,c_1802])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2186,plain,
    ( r2_relset_1(sK4,sK5,sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),X0)
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2349,plain,
    ( r2_relset_1(sK4,sK5,sK6,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_2350,plain,
    ( r2_relset_1(sK4,sK5,sK6,sK6) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2349])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2196,plain,
    ( r2_relset_1(sK4,sK5,sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),X0)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2361,plain,
    ( r2_relset_1(sK4,sK5,sK6,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_2362,plain,
    ( r2_relset_1(sK4,sK5,sK6,sK6) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2361])).

cnf(c_6816,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6755,c_38,c_2350,c_2362])).

cnf(c_6849,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6816,c_1800])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6855,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6849,c_7])).

cnf(c_7051,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6855])).

cnf(c_6850,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6816,c_1798])).

cnf(c_6852,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6850,c_7])).

cnf(c_7050,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6852])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4599,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
    | ~ r1_tarski(X0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4601,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_4599])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4049,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4051,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4049])).

cnf(c_2704,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2704])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k4_tarski(sK2(X1,X2,X3,X0),sK3(X1,X2,X3,X0)),X0)
    | r2_hidden(k4_tarski(sK2(X1,X2,X3,X0),sK3(X1,X2,X3,X0)),X3)
    | sK7 != X0
    | sK6 != X3
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_699,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_701,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
    | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_33,c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8041,c_7051,c_7050,c_4601,c_4051,c_2706,c_701])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.61/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.03  
% 3.61/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/1.03  
% 3.61/1.03  ------  iProver source info
% 3.61/1.03  
% 3.61/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.61/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/1.03  git: non_committed_changes: false
% 3.61/1.03  git: last_make_outside_of_git: false
% 3.61/1.03  
% 3.61/1.03  ------ 
% 3.61/1.03  
% 3.61/1.03  ------ Input Options
% 3.61/1.03  
% 3.61/1.03  --out_options                           all
% 3.61/1.03  --tptp_safe_out                         true
% 3.61/1.03  --problem_path                          ""
% 3.61/1.03  --include_path                          ""
% 3.61/1.03  --clausifier                            res/vclausify_rel
% 3.61/1.03  --clausifier_options                    --mode clausify
% 3.61/1.03  --stdin                                 false
% 3.61/1.03  --stats_out                             all
% 3.61/1.03  
% 3.61/1.03  ------ General Options
% 3.61/1.03  
% 3.61/1.03  --fof                                   false
% 3.61/1.03  --time_out_real                         305.
% 3.61/1.03  --time_out_virtual                      -1.
% 3.61/1.03  --symbol_type_check                     false
% 3.61/1.03  --clausify_out                          false
% 3.61/1.03  --sig_cnt_out                           false
% 3.61/1.03  --trig_cnt_out                          false
% 3.61/1.03  --trig_cnt_out_tolerance                1.
% 3.61/1.03  --trig_cnt_out_sk_spl                   false
% 3.61/1.03  --abstr_cl_out                          false
% 3.61/1.03  
% 3.61/1.03  ------ Global Options
% 3.61/1.03  
% 3.61/1.03  --schedule                              default
% 3.61/1.03  --add_important_lit                     false
% 3.61/1.03  --prop_solver_per_cl                    1000
% 3.61/1.03  --min_unsat_core                        false
% 3.61/1.03  --soft_assumptions                      false
% 3.61/1.03  --soft_lemma_size                       3
% 3.61/1.03  --prop_impl_unit_size                   0
% 3.61/1.03  --prop_impl_unit                        []
% 3.61/1.03  --share_sel_clauses                     true
% 3.61/1.03  --reset_solvers                         false
% 3.61/1.03  --bc_imp_inh                            [conj_cone]
% 3.61/1.03  --conj_cone_tolerance                   3.
% 3.61/1.03  --extra_neg_conj                        none
% 3.61/1.03  --large_theory_mode                     true
% 3.61/1.03  --prolific_symb_bound                   200
% 3.61/1.03  --lt_threshold                          2000
% 3.61/1.03  --clause_weak_htbl                      true
% 3.61/1.03  --gc_record_bc_elim                     false
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing Options
% 3.61/1.03  
% 3.61/1.03  --preprocessing_flag                    true
% 3.61/1.03  --time_out_prep_mult                    0.1
% 3.61/1.03  --splitting_mode                        input
% 3.61/1.03  --splitting_grd                         true
% 3.61/1.03  --splitting_cvd                         false
% 3.61/1.03  --splitting_cvd_svl                     false
% 3.61/1.03  --splitting_nvd                         32
% 3.61/1.03  --sub_typing                            true
% 3.61/1.03  --prep_gs_sim                           true
% 3.61/1.03  --prep_unflatten                        true
% 3.61/1.03  --prep_res_sim                          true
% 3.61/1.03  --prep_upred                            true
% 3.61/1.03  --prep_sem_filter                       exhaustive
% 3.61/1.03  --prep_sem_filter_out                   false
% 3.61/1.03  --pred_elim                             true
% 3.61/1.03  --res_sim_input                         true
% 3.61/1.03  --eq_ax_congr_red                       true
% 3.61/1.03  --pure_diseq_elim                       true
% 3.61/1.03  --brand_transform                       false
% 3.61/1.03  --non_eq_to_eq                          false
% 3.61/1.03  --prep_def_merge                        true
% 3.61/1.03  --prep_def_merge_prop_impl              false
% 3.61/1.03  --prep_def_merge_mbd                    true
% 3.61/1.03  --prep_def_merge_tr_red                 false
% 3.61/1.03  --prep_def_merge_tr_cl                  false
% 3.61/1.03  --smt_preprocessing                     true
% 3.61/1.03  --smt_ac_axioms                         fast
% 3.61/1.03  --preprocessed_out                      false
% 3.61/1.03  --preprocessed_stats                    false
% 3.61/1.03  
% 3.61/1.03  ------ Abstraction refinement Options
% 3.61/1.03  
% 3.61/1.03  --abstr_ref                             []
% 3.61/1.03  --abstr_ref_prep                        false
% 3.61/1.03  --abstr_ref_until_sat                   false
% 3.61/1.03  --abstr_ref_sig_restrict                funpre
% 3.61/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.03  --abstr_ref_under                       []
% 3.61/1.03  
% 3.61/1.03  ------ SAT Options
% 3.61/1.03  
% 3.61/1.03  --sat_mode                              false
% 3.61/1.03  --sat_fm_restart_options                ""
% 3.61/1.03  --sat_gr_def                            false
% 3.61/1.03  --sat_epr_types                         true
% 3.61/1.03  --sat_non_cyclic_types                  false
% 3.61/1.03  --sat_finite_models                     false
% 3.61/1.03  --sat_fm_lemmas                         false
% 3.61/1.03  --sat_fm_prep                           false
% 3.61/1.03  --sat_fm_uc_incr                        true
% 3.61/1.03  --sat_out_model                         small
% 3.61/1.03  --sat_out_clauses                       false
% 3.61/1.03  
% 3.61/1.03  ------ QBF Options
% 3.61/1.03  
% 3.61/1.03  --qbf_mode                              false
% 3.61/1.03  --qbf_elim_univ                         false
% 3.61/1.03  --qbf_dom_inst                          none
% 3.61/1.03  --qbf_dom_pre_inst                      false
% 3.61/1.03  --qbf_sk_in                             false
% 3.61/1.03  --qbf_pred_elim                         true
% 3.61/1.03  --qbf_split                             512
% 3.61/1.03  
% 3.61/1.03  ------ BMC1 Options
% 3.61/1.03  
% 3.61/1.03  --bmc1_incremental                      false
% 3.61/1.03  --bmc1_axioms                           reachable_all
% 3.61/1.03  --bmc1_min_bound                        0
% 3.61/1.03  --bmc1_max_bound                        -1
% 3.61/1.03  --bmc1_max_bound_default                -1
% 3.61/1.03  --bmc1_symbol_reachability              true
% 3.61/1.03  --bmc1_property_lemmas                  false
% 3.61/1.03  --bmc1_k_induction                      false
% 3.61/1.03  --bmc1_non_equiv_states                 false
% 3.61/1.03  --bmc1_deadlock                         false
% 3.61/1.03  --bmc1_ucm                              false
% 3.61/1.03  --bmc1_add_unsat_core                   none
% 3.61/1.03  --bmc1_unsat_core_children              false
% 3.61/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.03  --bmc1_out_stat                         full
% 3.61/1.03  --bmc1_ground_init                      false
% 3.61/1.03  --bmc1_pre_inst_next_state              false
% 3.61/1.03  --bmc1_pre_inst_state                   false
% 3.61/1.03  --bmc1_pre_inst_reach_state             false
% 3.61/1.03  --bmc1_out_unsat_core                   false
% 3.61/1.03  --bmc1_aig_witness_out                  false
% 3.61/1.03  --bmc1_verbose                          false
% 3.61/1.03  --bmc1_dump_clauses_tptp                false
% 3.61/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.03  --bmc1_dump_file                        -
% 3.61/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.03  --bmc1_ucm_extend_mode                  1
% 3.61/1.03  --bmc1_ucm_init_mode                    2
% 3.61/1.03  --bmc1_ucm_cone_mode                    none
% 3.61/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.03  --bmc1_ucm_relax_model                  4
% 3.61/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.03  --bmc1_ucm_layered_model                none
% 3.61/1.03  --bmc1_ucm_max_lemma_size               10
% 3.61/1.03  
% 3.61/1.03  ------ AIG Options
% 3.61/1.03  
% 3.61/1.03  --aig_mode                              false
% 3.61/1.03  
% 3.61/1.03  ------ Instantiation Options
% 3.61/1.03  
% 3.61/1.03  --instantiation_flag                    true
% 3.61/1.03  --inst_sos_flag                         false
% 3.61/1.03  --inst_sos_phase                        true
% 3.61/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.03  --inst_lit_sel_side                     num_symb
% 3.61/1.03  --inst_solver_per_active                1400
% 3.61/1.03  --inst_solver_calls_frac                1.
% 3.61/1.03  --inst_passive_queue_type               priority_queues
% 3.61/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.03  --inst_passive_queues_freq              [25;2]
% 3.61/1.03  --inst_dismatching                      true
% 3.61/1.03  --inst_eager_unprocessed_to_passive     true
% 3.61/1.03  --inst_prop_sim_given                   true
% 3.61/1.03  --inst_prop_sim_new                     false
% 3.61/1.03  --inst_subs_new                         false
% 3.61/1.03  --inst_eq_res_simp                      false
% 3.61/1.03  --inst_subs_given                       false
% 3.61/1.03  --inst_orphan_elimination               true
% 3.61/1.03  --inst_learning_loop_flag               true
% 3.61/1.03  --inst_learning_start                   3000
% 3.61/1.03  --inst_learning_factor                  2
% 3.61/1.03  --inst_start_prop_sim_after_learn       3
% 3.61/1.03  --inst_sel_renew                        solver
% 3.61/1.03  --inst_lit_activity_flag                true
% 3.61/1.03  --inst_restr_to_given                   false
% 3.61/1.03  --inst_activity_threshold               500
% 3.61/1.03  --inst_out_proof                        true
% 3.61/1.03  
% 3.61/1.03  ------ Resolution Options
% 3.61/1.03  
% 3.61/1.03  --resolution_flag                       true
% 3.61/1.03  --res_lit_sel                           adaptive
% 3.61/1.03  --res_lit_sel_side                      none
% 3.61/1.03  --res_ordering                          kbo
% 3.61/1.03  --res_to_prop_solver                    active
% 3.61/1.03  --res_prop_simpl_new                    false
% 3.61/1.03  --res_prop_simpl_given                  true
% 3.61/1.03  --res_passive_queue_type                priority_queues
% 3.61/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.03  --res_passive_queues_freq               [15;5]
% 3.61/1.03  --res_forward_subs                      full
% 3.61/1.03  --res_backward_subs                     full
% 3.61/1.03  --res_forward_subs_resolution           true
% 3.61/1.03  --res_backward_subs_resolution          true
% 3.61/1.03  --res_orphan_elimination                true
% 3.61/1.03  --res_time_limit                        2.
% 3.61/1.03  --res_out_proof                         true
% 3.61/1.03  
% 3.61/1.03  ------ Superposition Options
% 3.61/1.03  
% 3.61/1.03  --superposition_flag                    true
% 3.61/1.03  --sup_passive_queue_type                priority_queues
% 3.61/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.03  --demod_completeness_check              fast
% 3.61/1.03  --demod_use_ground                      true
% 3.61/1.03  --sup_to_prop_solver                    passive
% 3.61/1.03  --sup_prop_simpl_new                    true
% 3.61/1.03  --sup_prop_simpl_given                  true
% 3.61/1.03  --sup_fun_splitting                     false
% 3.61/1.03  --sup_smt_interval                      50000
% 3.61/1.03  
% 3.61/1.03  ------ Superposition Simplification Setup
% 3.61/1.03  
% 3.61/1.03  --sup_indices_passive                   []
% 3.61/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_full_bw                           [BwDemod]
% 3.61/1.03  --sup_immed_triv                        [TrivRules]
% 3.61/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_immed_bw_main                     []
% 3.61/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/1.03  
% 3.61/1.03  ------ Combination Options
% 3.61/1.03  
% 3.61/1.03  --comb_res_mult                         3
% 3.61/1.03  --comb_sup_mult                         2
% 3.61/1.03  --comb_inst_mult                        10
% 3.61/1.03  
% 3.61/1.03  ------ Debug Options
% 3.61/1.03  
% 3.61/1.03  --dbg_backtrace                         false
% 3.61/1.03  --dbg_dump_prop_clauses                 false
% 3.61/1.03  --dbg_dump_prop_clauses_file            -
% 3.61/1.03  --dbg_out_stat                          false
% 3.61/1.03  ------ Parsing...
% 3.61/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.03  ------ Proving...
% 3.61/1.03  ------ Problem Properties 
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  clauses                                 33
% 3.61/1.03  conjectures                             6
% 3.61/1.03  EPR                                     8
% 3.61/1.03  Horn                                    23
% 3.61/1.03  unary                                   9
% 3.61/1.03  binary                                  8
% 3.61/1.03  lits                                    97
% 3.61/1.03  lits eq                                 27
% 3.61/1.03  fd_pure                                 0
% 3.61/1.03  fd_pseudo                               0
% 3.61/1.03  fd_cond                                 1
% 3.61/1.03  fd_pseudo_cond                          3
% 3.61/1.03  AC symbols                              0
% 3.61/1.03  
% 3.61/1.03  ------ Schedule dynamic 5 is on 
% 3.61/1.03  
% 3.61/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  ------ 
% 3.61/1.03  Current options:
% 3.61/1.03  ------ 
% 3.61/1.03  
% 3.61/1.03  ------ Input Options
% 3.61/1.03  
% 3.61/1.03  --out_options                           all
% 3.61/1.03  --tptp_safe_out                         true
% 3.61/1.03  --problem_path                          ""
% 3.61/1.03  --include_path                          ""
% 3.61/1.03  --clausifier                            res/vclausify_rel
% 3.61/1.03  --clausifier_options                    --mode clausify
% 3.61/1.03  --stdin                                 false
% 3.61/1.03  --stats_out                             all
% 3.61/1.03  
% 3.61/1.03  ------ General Options
% 3.61/1.03  
% 3.61/1.03  --fof                                   false
% 3.61/1.03  --time_out_real                         305.
% 3.61/1.03  --time_out_virtual                      -1.
% 3.61/1.03  --symbol_type_check                     false
% 3.61/1.03  --clausify_out                          false
% 3.61/1.03  --sig_cnt_out                           false
% 3.61/1.03  --trig_cnt_out                          false
% 3.61/1.03  --trig_cnt_out_tolerance                1.
% 3.61/1.03  --trig_cnt_out_sk_spl                   false
% 3.61/1.03  --abstr_cl_out                          false
% 3.61/1.03  
% 3.61/1.03  ------ Global Options
% 3.61/1.03  
% 3.61/1.03  --schedule                              default
% 3.61/1.03  --add_important_lit                     false
% 3.61/1.03  --prop_solver_per_cl                    1000
% 3.61/1.03  --min_unsat_core                        false
% 3.61/1.03  --soft_assumptions                      false
% 3.61/1.03  --soft_lemma_size                       3
% 3.61/1.03  --prop_impl_unit_size                   0
% 3.61/1.03  --prop_impl_unit                        []
% 3.61/1.03  --share_sel_clauses                     true
% 3.61/1.03  --reset_solvers                         false
% 3.61/1.03  --bc_imp_inh                            [conj_cone]
% 3.61/1.03  --conj_cone_tolerance                   3.
% 3.61/1.03  --extra_neg_conj                        none
% 3.61/1.03  --large_theory_mode                     true
% 3.61/1.03  --prolific_symb_bound                   200
% 3.61/1.03  --lt_threshold                          2000
% 3.61/1.03  --clause_weak_htbl                      true
% 3.61/1.03  --gc_record_bc_elim                     false
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing Options
% 3.61/1.03  
% 3.61/1.03  --preprocessing_flag                    true
% 3.61/1.03  --time_out_prep_mult                    0.1
% 3.61/1.03  --splitting_mode                        input
% 3.61/1.03  --splitting_grd                         true
% 3.61/1.03  --splitting_cvd                         false
% 3.61/1.03  --splitting_cvd_svl                     false
% 3.61/1.03  --splitting_nvd                         32
% 3.61/1.03  --sub_typing                            true
% 3.61/1.03  --prep_gs_sim                           true
% 3.61/1.03  --prep_unflatten                        true
% 3.61/1.03  --prep_res_sim                          true
% 3.61/1.03  --prep_upred                            true
% 3.61/1.03  --prep_sem_filter                       exhaustive
% 3.61/1.03  --prep_sem_filter_out                   false
% 3.61/1.03  --pred_elim                             true
% 3.61/1.03  --res_sim_input                         true
% 3.61/1.03  --eq_ax_congr_red                       true
% 3.61/1.03  --pure_diseq_elim                       true
% 3.61/1.03  --brand_transform                       false
% 3.61/1.03  --non_eq_to_eq                          false
% 3.61/1.03  --prep_def_merge                        true
% 3.61/1.03  --prep_def_merge_prop_impl              false
% 3.61/1.03  --prep_def_merge_mbd                    true
% 3.61/1.03  --prep_def_merge_tr_red                 false
% 3.61/1.03  --prep_def_merge_tr_cl                  false
% 3.61/1.03  --smt_preprocessing                     true
% 3.61/1.03  --smt_ac_axioms                         fast
% 3.61/1.03  --preprocessed_out                      false
% 3.61/1.03  --preprocessed_stats                    false
% 3.61/1.03  
% 3.61/1.03  ------ Abstraction refinement Options
% 3.61/1.03  
% 3.61/1.03  --abstr_ref                             []
% 3.61/1.03  --abstr_ref_prep                        false
% 3.61/1.03  --abstr_ref_until_sat                   false
% 3.61/1.03  --abstr_ref_sig_restrict                funpre
% 3.61/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.03  --abstr_ref_under                       []
% 3.61/1.03  
% 3.61/1.03  ------ SAT Options
% 3.61/1.03  
% 3.61/1.03  --sat_mode                              false
% 3.61/1.03  --sat_fm_restart_options                ""
% 3.61/1.03  --sat_gr_def                            false
% 3.61/1.03  --sat_epr_types                         true
% 3.61/1.03  --sat_non_cyclic_types                  false
% 3.61/1.03  --sat_finite_models                     false
% 3.61/1.03  --sat_fm_lemmas                         false
% 3.61/1.03  --sat_fm_prep                           false
% 3.61/1.03  --sat_fm_uc_incr                        true
% 3.61/1.03  --sat_out_model                         small
% 3.61/1.03  --sat_out_clauses                       false
% 3.61/1.03  
% 3.61/1.03  ------ QBF Options
% 3.61/1.03  
% 3.61/1.03  --qbf_mode                              false
% 3.61/1.03  --qbf_elim_univ                         false
% 3.61/1.03  --qbf_dom_inst                          none
% 3.61/1.03  --qbf_dom_pre_inst                      false
% 3.61/1.03  --qbf_sk_in                             false
% 3.61/1.03  --qbf_pred_elim                         true
% 3.61/1.03  --qbf_split                             512
% 3.61/1.03  
% 3.61/1.03  ------ BMC1 Options
% 3.61/1.03  
% 3.61/1.03  --bmc1_incremental                      false
% 3.61/1.03  --bmc1_axioms                           reachable_all
% 3.61/1.03  --bmc1_min_bound                        0
% 3.61/1.03  --bmc1_max_bound                        -1
% 3.61/1.03  --bmc1_max_bound_default                -1
% 3.61/1.03  --bmc1_symbol_reachability              true
% 3.61/1.03  --bmc1_property_lemmas                  false
% 3.61/1.03  --bmc1_k_induction                      false
% 3.61/1.03  --bmc1_non_equiv_states                 false
% 3.61/1.03  --bmc1_deadlock                         false
% 3.61/1.03  --bmc1_ucm                              false
% 3.61/1.03  --bmc1_add_unsat_core                   none
% 3.61/1.03  --bmc1_unsat_core_children              false
% 3.61/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.03  --bmc1_out_stat                         full
% 3.61/1.03  --bmc1_ground_init                      false
% 3.61/1.03  --bmc1_pre_inst_next_state              false
% 3.61/1.03  --bmc1_pre_inst_state                   false
% 3.61/1.03  --bmc1_pre_inst_reach_state             false
% 3.61/1.03  --bmc1_out_unsat_core                   false
% 3.61/1.03  --bmc1_aig_witness_out                  false
% 3.61/1.03  --bmc1_verbose                          false
% 3.61/1.03  --bmc1_dump_clauses_tptp                false
% 3.61/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.03  --bmc1_dump_file                        -
% 3.61/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.03  --bmc1_ucm_extend_mode                  1
% 3.61/1.03  --bmc1_ucm_init_mode                    2
% 3.61/1.03  --bmc1_ucm_cone_mode                    none
% 3.61/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.03  --bmc1_ucm_relax_model                  4
% 3.61/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.03  --bmc1_ucm_layered_model                none
% 3.61/1.03  --bmc1_ucm_max_lemma_size               10
% 3.61/1.03  
% 3.61/1.03  ------ AIG Options
% 3.61/1.03  
% 3.61/1.03  --aig_mode                              false
% 3.61/1.03  
% 3.61/1.03  ------ Instantiation Options
% 3.61/1.03  
% 3.61/1.03  --instantiation_flag                    true
% 3.61/1.03  --inst_sos_flag                         false
% 3.61/1.03  --inst_sos_phase                        true
% 3.61/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.03  --inst_lit_sel_side                     none
% 3.61/1.03  --inst_solver_per_active                1400
% 3.61/1.03  --inst_solver_calls_frac                1.
% 3.61/1.03  --inst_passive_queue_type               priority_queues
% 3.61/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.03  --inst_passive_queues_freq              [25;2]
% 3.61/1.03  --inst_dismatching                      true
% 3.61/1.03  --inst_eager_unprocessed_to_passive     true
% 3.61/1.03  --inst_prop_sim_given                   true
% 3.61/1.03  --inst_prop_sim_new                     false
% 3.61/1.03  --inst_subs_new                         false
% 3.61/1.03  --inst_eq_res_simp                      false
% 3.61/1.03  --inst_subs_given                       false
% 3.61/1.03  --inst_orphan_elimination               true
% 3.61/1.03  --inst_learning_loop_flag               true
% 3.61/1.03  --inst_learning_start                   3000
% 3.61/1.03  --inst_learning_factor                  2
% 3.61/1.03  --inst_start_prop_sim_after_learn       3
% 3.61/1.03  --inst_sel_renew                        solver
% 3.61/1.03  --inst_lit_activity_flag                true
% 3.61/1.03  --inst_restr_to_given                   false
% 3.61/1.03  --inst_activity_threshold               500
% 3.61/1.03  --inst_out_proof                        true
% 3.61/1.03  
% 3.61/1.03  ------ Resolution Options
% 3.61/1.03  
% 3.61/1.03  --resolution_flag                       false
% 3.61/1.03  --res_lit_sel                           adaptive
% 3.61/1.03  --res_lit_sel_side                      none
% 3.61/1.03  --res_ordering                          kbo
% 3.61/1.03  --res_to_prop_solver                    active
% 3.61/1.03  --res_prop_simpl_new                    false
% 3.61/1.03  --res_prop_simpl_given                  true
% 3.61/1.03  --res_passive_queue_type                priority_queues
% 3.61/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.03  --res_passive_queues_freq               [15;5]
% 3.61/1.03  --res_forward_subs                      full
% 3.61/1.03  --res_backward_subs                     full
% 3.61/1.03  --res_forward_subs_resolution           true
% 3.61/1.03  --res_backward_subs_resolution          true
% 3.61/1.03  --res_orphan_elimination                true
% 3.61/1.03  --res_time_limit                        2.
% 3.61/1.03  --res_out_proof                         true
% 3.61/1.03  
% 3.61/1.03  ------ Superposition Options
% 3.61/1.03  
% 3.61/1.03  --superposition_flag                    true
% 3.61/1.03  --sup_passive_queue_type                priority_queues
% 3.61/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.03  --demod_completeness_check              fast
% 3.61/1.03  --demod_use_ground                      true
% 3.61/1.03  --sup_to_prop_solver                    passive
% 3.61/1.03  --sup_prop_simpl_new                    true
% 3.61/1.03  --sup_prop_simpl_given                  true
% 3.61/1.03  --sup_fun_splitting                     false
% 3.61/1.03  --sup_smt_interval                      50000
% 3.61/1.03  
% 3.61/1.03  ------ Superposition Simplification Setup
% 3.61/1.03  
% 3.61/1.03  --sup_indices_passive                   []
% 3.61/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_full_bw                           [BwDemod]
% 3.61/1.03  --sup_immed_triv                        [TrivRules]
% 3.61/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_immed_bw_main                     []
% 3.61/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/1.03  
% 3.61/1.03  ------ Combination Options
% 3.61/1.03  
% 3.61/1.03  --comb_res_mult                         3
% 3.61/1.03  --comb_sup_mult                         2
% 3.61/1.03  --comb_inst_mult                        10
% 3.61/1.03  
% 3.61/1.03  ------ Debug Options
% 3.61/1.03  
% 3.61/1.03  --dbg_backtrace                         false
% 3.61/1.03  --dbg_dump_prop_clauses                 false
% 3.61/1.03  --dbg_dump_prop_clauses_file            -
% 3.61/1.03  --dbg_out_stat                          false
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  ------ Proving...
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  % SZS status Theorem for theBenchmark.p
% 3.61/1.03  
% 3.61/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/1.03  
% 3.61/1.03  fof(f3,axiom,(
% 3.61/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f52,plain,(
% 3.61/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.61/1.03    inference(cnf_transformation,[],[f3])).
% 3.61/1.03  
% 3.61/1.03  fof(f11,axiom,(
% 3.61/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f22,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(ennf_transformation,[],[f11])).
% 3.61/1.03  
% 3.61/1.03  fof(f23,plain,(
% 3.61/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(flattening,[],[f22])).
% 3.61/1.03  
% 3.61/1.03  fof(f42,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(nnf_transformation,[],[f23])).
% 3.61/1.03  
% 3.61/1.03  fof(f68,plain,(
% 3.61/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f42])).
% 3.61/1.03  
% 3.61/1.03  fof(f12,conjecture,(
% 3.61/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f13,negated_conjecture,(
% 3.61/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.61/1.03    inference(negated_conjecture,[],[f12])).
% 3.61/1.03  
% 3.61/1.03  fof(f24,plain,(
% 3.61/1.03    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.61/1.03    inference(ennf_transformation,[],[f13])).
% 3.61/1.03  
% 3.61/1.03  fof(f25,plain,(
% 3.61/1.03    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.61/1.03    inference(flattening,[],[f24])).
% 3.61/1.03  
% 3.61/1.03  fof(f44,plain,(
% 3.61/1.03    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK7) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK7,X0,X1) & v1_funct_1(sK7))) )),
% 3.61/1.03    introduced(choice_axiom,[])).
% 3.61/1.03  
% 3.61/1.03  fof(f43,plain,(
% 3.61/1.03    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK4,sK5,sK6,X3) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.61/1.03    introduced(choice_axiom,[])).
% 3.61/1.03  
% 3.61/1.03  fof(f45,plain,(
% 3.61/1.03    (~r2_relset_1(sK4,sK5,sK6,sK7) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.61/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f44,f43])).
% 3.61/1.03  
% 3.61/1.03  fof(f75,plain,(
% 3.61/1.03    v1_funct_2(sK6,sK4,sK5)),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f76,plain,(
% 3.61/1.03    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f10,axiom,(
% 3.61/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f21,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(ennf_transformation,[],[f10])).
% 3.61/1.03  
% 3.61/1.03  fof(f67,plain,(
% 3.61/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f21])).
% 3.61/1.03  
% 3.61/1.03  fof(f78,plain,(
% 3.61/1.03    v1_funct_2(sK7,sK4,sK5)),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f79,plain,(
% 3.61/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f6,axiom,(
% 3.61/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f16,plain,(
% 3.61/1.03    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/1.03    inference(ennf_transformation,[],[f6])).
% 3.61/1.03  
% 3.61/1.03  fof(f17,plain,(
% 3.61/1.03    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/1.03    inference(flattening,[],[f16])).
% 3.61/1.03  
% 3.61/1.03  fof(f34,plain,(
% 3.61/1.03    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.61/1.03    introduced(choice_axiom,[])).
% 3.61/1.03  
% 3.61/1.03  fof(f35,plain,(
% 3.61/1.03    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f34])).
% 3.61/1.03  
% 3.61/1.03  fof(f57,plain,(
% 3.61/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/1.03    inference(cnf_transformation,[],[f35])).
% 3.61/1.03  
% 3.61/1.03  fof(f77,plain,(
% 3.61/1.03    v1_funct_1(sK7)),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f8,axiom,(
% 3.61/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f19,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(ennf_transformation,[],[f8])).
% 3.61/1.03  
% 3.61/1.03  fof(f60,plain,(
% 3.61/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f19])).
% 3.61/1.03  
% 3.61/1.03  fof(f74,plain,(
% 3.61/1.03    v1_funct_1(sK6)),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f80,plain,(
% 3.61/1.03    ( ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK4)) )),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f58,plain,(
% 3.61/1.03    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/1.03    inference(cnf_transformation,[],[f35])).
% 3.61/1.03  
% 3.61/1.03  fof(f81,plain,(
% 3.61/1.03    ~r2_relset_1(sK4,sK5,sK6,sK7)),
% 3.61/1.03    inference(cnf_transformation,[],[f45])).
% 3.61/1.03  
% 3.61/1.03  fof(f9,axiom,(
% 3.61/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f20,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(ennf_transformation,[],[f9])).
% 3.61/1.03  
% 3.61/1.03  fof(f36,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(nnf_transformation,[],[f20])).
% 3.61/1.03  
% 3.61/1.03  fof(f37,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(flattening,[],[f36])).
% 3.61/1.03  
% 3.61/1.03  fof(f38,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(rectify,[],[f37])).
% 3.61/1.03  
% 3.61/1.03  fof(f40,plain,(
% 3.61/1.03    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK3(X0,X1,X2,X3)),X2)) & m1_subset_1(sK3(X0,X1,X2,X3),X1)))) )),
% 3.61/1.03    introduced(choice_axiom,[])).
% 3.61/1.03  
% 3.61/1.03  fof(f39,plain,(
% 3.61/1.03    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK2(X0,X1,X2,X3),X0)))),
% 3.61/1.03    introduced(choice_axiom,[])).
% 3.61/1.03  
% 3.61/1.03  fof(f41,plain,(
% 3.61/1.03    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2)) & m1_subset_1(sK3(X0,X1,X2,X3),X1)) & m1_subset_1(sK2(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 3.61/1.03  
% 3.61/1.03  fof(f66,plain,(
% 3.61/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f41])).
% 3.61/1.03  
% 3.61/1.03  fof(f65,plain,(
% 3.61/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f41])).
% 3.61/1.03  
% 3.61/1.03  fof(f4,axiom,(
% 3.61/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f32,plain,(
% 3.61/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.61/1.03    inference(nnf_transformation,[],[f4])).
% 3.61/1.03  
% 3.61/1.03  fof(f33,plain,(
% 3.61/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.61/1.03    inference(flattening,[],[f32])).
% 3.61/1.03  
% 3.61/1.03  fof(f55,plain,(
% 3.61/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.61/1.03    inference(cnf_transformation,[],[f33])).
% 3.61/1.03  
% 3.61/1.03  fof(f84,plain,(
% 3.61/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.61/1.03    inference(equality_resolution,[],[f55])).
% 3.61/1.03  
% 3.61/1.03  fof(f7,axiom,(
% 3.61/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f18,plain,(
% 3.61/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.61/1.03    inference(ennf_transformation,[],[f7])).
% 3.61/1.03  
% 3.61/1.03  fof(f59,plain,(
% 3.61/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.61/1.03    inference(cnf_transformation,[],[f18])).
% 3.61/1.03  
% 3.61/1.03  fof(f5,axiom,(
% 3.61/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.61/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.03  
% 3.61/1.03  fof(f15,plain,(
% 3.61/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.03    inference(ennf_transformation,[],[f5])).
% 3.61/1.03  
% 3.61/1.03  fof(f56,plain,(
% 3.61/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/1.03    inference(cnf_transformation,[],[f15])).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6,plain,
% 3.61/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_8041,plain,
% 3.61/1.03      ( r1_tarski(k1_xboole_0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_27,plain,
% 3.61/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.61/1.03      | k1_xboole_0 = X2 ),
% 3.61/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_34,negated_conjecture,
% 3.61/1.03      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.61/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_439,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.61/1.03      | sK6 != X0
% 3.61/1.03      | sK5 != X2
% 3.61/1.03      | sK4 != X1
% 3.61/1.03      | k1_xboole_0 = X2 ),
% 3.61/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_440,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.61/1.03      | k1_xboole_0 = sK5 ),
% 3.61/1.03      inference(unflattening,[status(thm)],[c_439]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_33,negated_conjecture,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.61/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_442,plain,
% 3.61/1.03      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_440,c_33]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1798,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_21,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1803,plain,
% 3.61/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2205,plain,
% 3.61/1.03      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_1798,c_1803]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2478,plain,
% 3.61/1.03      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_442,c_2205]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_31,negated_conjecture,
% 3.61/1.03      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.61/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_428,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.61/1.03      | sK7 != X0
% 3.61/1.03      | sK5 != X2
% 3.61/1.03      | sK4 != X1
% 3.61/1.03      | k1_xboole_0 = X2 ),
% 3.61/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_429,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.61/1.03      | k1_xboole_0 = sK5 ),
% 3.61/1.03      inference(unflattening,[status(thm)],[c_428]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_30,negated_conjecture,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.61/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_431,plain,
% 3.61/1.03      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_429,c_30]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1800,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2204,plain,
% 3.61/1.03      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_1800,c_1803]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2425,plain,
% 3.61/1.03      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_431,c_2204]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_12,plain,
% 3.61/1.03      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.61/1.03      | ~ v1_relat_1(X1)
% 3.61/1.03      | ~ v1_relat_1(X0)
% 3.61/1.03      | ~ v1_funct_1(X1)
% 3.61/1.03      | ~ v1_funct_1(X0)
% 3.61/1.03      | X1 = X0
% 3.61/1.03      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1812,plain,
% 3.61/1.03      ( X0 = X1
% 3.61/1.03      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.61/1.03      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.61/1.03      | v1_relat_1(X1) != iProver_top
% 3.61/1.03      | v1_relat_1(X0) != iProver_top
% 3.61/1.03      | v1_funct_1(X0) != iProver_top
% 3.61/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_4675,plain,
% 3.61/1.03      ( k1_relat_1(X0) != sK4
% 3.61/1.03      | sK7 = X0
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.61/1.03      | v1_relat_1(X0) != iProver_top
% 3.61/1.03      | v1_relat_1(sK7) != iProver_top
% 3.61/1.03      | v1_funct_1(X0) != iProver_top
% 3.61/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_2425,c_1812]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_32,negated_conjecture,
% 3.61/1.03      ( v1_funct_1(sK7) ),
% 3.61/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_39,plain,
% 3.61/1.03      ( v1_funct_1(sK7) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_41,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_14,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | v1_relat_1(X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2084,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | v1_relat_1(sK7) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2085,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.61/1.03      | v1_relat_1(sK7) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5714,plain,
% 3.61/1.03      ( v1_funct_1(X0) != iProver_top
% 3.61/1.03      | k1_relat_1(X0) != sK4
% 3.61/1.03      | sK7 = X0
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.61/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_4675,c_39,c_41,c_2085]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5715,plain,
% 3.61/1.03      ( k1_relat_1(X0) != sK4
% 3.61/1.03      | sK7 = X0
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.61/1.03      | v1_relat_1(X0) != iProver_top
% 3.61/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.61/1.03      inference(renaming,[status(thm)],[c_5714]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5727,plain,
% 3.61/1.03      ( sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
% 3.61/1.03      | v1_relat_1(sK6) != iProver_top
% 3.61/1.03      | v1_funct_1(sK6) != iProver_top ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_2478,c_5715]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_35,negated_conjecture,
% 3.61/1.03      ( v1_funct_1(sK6) ),
% 3.61/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_36,plain,
% 3.61/1.03      ( v1_funct_1(sK6) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_38,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2087,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | v1_relat_1(sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2088,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.61/1.03      | v1_relat_1(sK6) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5865,plain,
% 3.61/1.03      ( sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_5727,c_36,c_38,c_2088]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5872,plain,
% 3.61/1.03      ( sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | r2_hidden(sK1(sK6,sK7),sK4) = iProver_top ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_2478,c_5865]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_29,negated_conjecture,
% 3.61/1.03      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1801,plain,
% 3.61/1.03      ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
% 3.61/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_5906,plain,
% 3.61/1.03      ( k1_funct_1(sK6,sK1(sK6,sK7)) = k1_funct_1(sK7,sK1(sK6,sK7))
% 3.61/1.03      | sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_5872,c_1801]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_11,plain,
% 3.61/1.03      ( ~ v1_relat_1(X0)
% 3.61/1.03      | ~ v1_relat_1(X1)
% 3.61/1.03      | ~ v1_funct_1(X0)
% 3.61/1.03      | ~ v1_funct_1(X1)
% 3.61/1.03      | X0 = X1
% 3.61/1.03      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.61/1.03      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.61/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1813,plain,
% 3.61/1.03      ( X0 = X1
% 3.61/1.03      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.61/1.03      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.61/1.03      | v1_relat_1(X0) != iProver_top
% 3.61/1.03      | v1_relat_1(X1) != iProver_top
% 3.61/1.03      | v1_funct_1(X1) != iProver_top
% 3.61/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6534,plain,
% 3.61/1.03      ( k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.61/1.03      | sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0
% 3.61/1.03      | v1_relat_1(sK7) != iProver_top
% 3.61/1.03      | v1_relat_1(sK6) != iProver_top
% 3.61/1.03      | v1_funct_1(sK7) != iProver_top
% 3.61/1.03      | v1_funct_1(sK6) != iProver_top ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_5906,c_1813]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1301,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2842,plain,
% 3.61/1.03      ( k1_relat_1(sK7) != X0
% 3.61/1.03      | k1_relat_1(sK6) != X0
% 3.61/1.03      | k1_relat_1(sK6) = k1_relat_1(sK7) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_1301]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6382,plain,
% 3.61/1.03      ( k1_relat_1(sK7) != sK4
% 3.61/1.03      | k1_relat_1(sK6) = k1_relat_1(sK7)
% 3.61/1.03      | k1_relat_1(sK6) != sK4 ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_2842]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6535,plain,
% 3.61/1.03      ( ~ v1_relat_1(sK7)
% 3.61/1.03      | ~ v1_relat_1(sK6)
% 3.61/1.03      | ~ v1_funct_1(sK7)
% 3.61/1.03      | ~ v1_funct_1(sK6)
% 3.61/1.03      | k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.61/1.03      | sK7 = sK6
% 3.61/1.03      | sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_6534]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6739,plain,
% 3.61/1.03      ( sK7 = sK6 | sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_6534,c_35,c_33,c_32,c_30,c_2084,c_2087,c_2425,c_2478,
% 3.61/1.03                 c_6382,c_6535]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_28,negated_conjecture,
% 3.61/1.03      ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
% 3.61/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_1802,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,sK7) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6755,plain,
% 3.61/1.03      ( sK5 = k1_xboole_0 | r2_relset_1(sK4,sK5,sK6,sK6) != iProver_top ),
% 3.61/1.03      inference(superposition,[status(thm)],[c_6739,c_1802]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_15,plain,
% 3.61/1.03      ( r2_relset_1(X0,X1,X2,X3)
% 3.61/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
% 3.61/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2186,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,X0)
% 3.61/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),X0)
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2349,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,sK6)
% 3.61/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_2186]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2350,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,sK6) = iProver_top
% 3.61/1.03      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) != iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_2349]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_16,plain,
% 3.61/1.03      ( r2_relset_1(X0,X1,X2,X3)
% 3.61/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X3)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(X0,X1,X2,X3),sK3(X0,X1,X2,X3)),X2) ),
% 3.61/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2196,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,X0)
% 3.61/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),X0)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,X0),sK3(sK4,sK5,sK6,X0)),sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2361,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,sK6)
% 3.61/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_2196]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2362,plain,
% 3.61/1.03      ( r2_relset_1(sK4,sK5,sK6,sK6) = iProver_top
% 3.61/1.03      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK6),sK3(sK4,sK5,sK6,sK6)),sK6) = iProver_top ),
% 3.61/1.03      inference(predicate_to_equality,[status(thm)],[c_2361]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6816,plain,
% 3.61/1.03      ( sK5 = k1_xboole_0 ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_6755,c_38,c_2350,c_2362]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6849,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.61/1.03      inference(demodulation,[status(thm)],[c_6816,c_1800]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_7,plain,
% 3.61/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.61/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6855,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.61/1.03      inference(demodulation,[status(thm)],[c_6849,c_7]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_7051,plain,
% 3.61/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) ),
% 3.61/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_6855]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6850,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.61/1.03      inference(demodulation,[status(thm)],[c_6816,c_1798]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_6852,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.61/1.03      inference(demodulation,[status(thm)],[c_6850,c_7]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_7050,plain,
% 3.61/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
% 3.61/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_6852]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_13,plain,
% 3.61/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.61/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_4599,plain,
% 3.61/1.03      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
% 3.61/1.03      | ~ r1_tarski(X0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_4601,plain,
% 3.61/1.03      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0)
% 3.61/1.03      | ~ r1_tarski(k1_xboole_0,k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7))) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_4599]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_10,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.03      | ~ r2_hidden(X2,X0)
% 3.61/1.03      | r2_hidden(X2,X1) ),
% 3.61/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_4049,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_4051,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_4049]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2704,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),X0)
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_2706,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
% 3.61/1.03      | ~ r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),k1_xboole_0) ),
% 3.61/1.03      inference(instantiation,[status(thm)],[c_2704]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_698,plain,
% 3.61/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(X1,X2,X3,X0),sK3(X1,X2,X3,X0)),X0)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(X1,X2,X3,X0),sK3(X1,X2,X3,X0)),X3)
% 3.61/1.03      | sK7 != X0
% 3.61/1.03      | sK6 != X3
% 3.61/1.03      | sK5 != X2
% 3.61/1.03      | sK4 != X1 ),
% 3.61/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_699,plain,
% 3.61/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
% 3.61/1.03      inference(unflattening,[status(thm)],[c_698]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(c_701,plain,
% 3.61/1.03      ( r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK7)
% 3.61/1.03      | r2_hidden(k4_tarski(sK2(sK4,sK5,sK6,sK7),sK3(sK4,sK5,sK6,sK7)),sK6) ),
% 3.61/1.03      inference(global_propositional_subsumption,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_699,c_33,c_30]) ).
% 3.61/1.03  
% 3.61/1.03  cnf(contradiction,plain,
% 3.61/1.03      ( $false ),
% 3.61/1.03      inference(minisat,
% 3.61/1.03                [status(thm)],
% 3.61/1.03                [c_8041,c_7051,c_7050,c_4601,c_4051,c_2706,c_701]) ).
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/1.03  
% 3.61/1.03  ------                               Statistics
% 3.61/1.03  
% 3.61/1.03  ------ General
% 3.61/1.03  
% 3.61/1.03  abstr_ref_over_cycles:                  0
% 3.61/1.03  abstr_ref_under_cycles:                 0
% 3.61/1.03  gc_basic_clause_elim:                   0
% 3.61/1.03  forced_gc_time:                         0
% 3.61/1.03  parsing_time:                           0.013
% 3.61/1.03  unif_index_cands_time:                  0.
% 3.61/1.03  unif_index_add_time:                    0.
% 3.61/1.03  orderings_time:                         0.
% 3.61/1.03  out_proof_time:                         0.013
% 3.61/1.03  total_time:                             0.253
% 3.61/1.03  num_of_symbols:                         53
% 3.61/1.03  num_of_terms:                           6809
% 3.61/1.03  
% 3.61/1.03  ------ Preprocessing
% 3.61/1.03  
% 3.61/1.03  num_of_splits:                          0
% 3.61/1.03  num_of_split_atoms:                     0
% 3.61/1.03  num_of_reused_defs:                     0
% 3.61/1.03  num_eq_ax_congr_red:                    47
% 3.61/1.03  num_of_sem_filtered_clauses:            1
% 3.61/1.03  num_of_subtypes:                        0
% 3.61/1.03  monotx_restored_types:                  0
% 3.61/1.03  sat_num_of_epr_types:                   0
% 3.61/1.03  sat_num_of_non_cyclic_types:            0
% 3.61/1.03  sat_guarded_non_collapsed_types:        0
% 3.61/1.03  num_pure_diseq_elim:                    0
% 3.61/1.03  simp_replaced_by:                       0
% 3.61/1.03  res_preprocessed:                       159
% 3.61/1.03  prep_upred:                             0
% 3.61/1.03  prep_unflattend:                        66
% 3.61/1.03  smt_new_axioms:                         0
% 3.61/1.03  pred_elim_cands:                        6
% 3.61/1.03  pred_elim:                              1
% 3.61/1.03  pred_elim_cl:                           2
% 3.61/1.03  pred_elim_cycles:                       3
% 3.61/1.03  merged_defs:                            0
% 3.61/1.03  merged_defs_ncl:                        0
% 3.61/1.03  bin_hyper_res:                          0
% 3.61/1.03  prep_cycles:                            4
% 3.61/1.03  pred_elim_time:                         0.014
% 3.61/1.03  splitting_time:                         0.
% 3.61/1.03  sem_filter_time:                        0.
% 3.61/1.03  monotx_time:                            0.001
% 3.61/1.03  subtype_inf_time:                       0.
% 3.61/1.03  
% 3.61/1.03  ------ Problem properties
% 3.61/1.03  
% 3.61/1.03  clauses:                                33
% 3.61/1.03  conjectures:                            6
% 3.61/1.03  epr:                                    8
% 3.61/1.03  horn:                                   23
% 3.61/1.03  ground:                                 11
% 3.61/1.03  unary:                                  9
% 3.61/1.03  binary:                                 8
% 3.61/1.03  lits:                                   97
% 3.61/1.03  lits_eq:                                27
% 3.61/1.03  fd_pure:                                0
% 3.61/1.03  fd_pseudo:                              0
% 3.61/1.03  fd_cond:                                1
% 3.61/1.03  fd_pseudo_cond:                         3
% 3.61/1.03  ac_symbols:                             0
% 3.61/1.03  
% 3.61/1.03  ------ Propositional Solver
% 3.61/1.03  
% 3.61/1.03  prop_solver_calls:                      27
% 3.61/1.03  prop_fast_solver_calls:                 1419
% 3.61/1.03  smt_solver_calls:                       0
% 3.61/1.03  smt_fast_solver_calls:                  0
% 3.61/1.03  prop_num_of_clauses:                    2489
% 3.61/1.03  prop_preprocess_simplified:             8217
% 3.61/1.03  prop_fo_subsumed:                       28
% 3.61/1.03  prop_solver_time:                       0.
% 3.61/1.03  smt_solver_time:                        0.
% 3.61/1.03  smt_fast_solver_time:                   0.
% 3.61/1.03  prop_fast_solver_time:                  0.
% 3.61/1.03  prop_unsat_core_time:                   0.
% 3.61/1.03  
% 3.61/1.03  ------ QBF
% 3.61/1.03  
% 3.61/1.03  qbf_q_res:                              0
% 3.61/1.03  qbf_num_tautologies:                    0
% 3.61/1.03  qbf_prep_cycles:                        0
% 3.61/1.03  
% 3.61/1.03  ------ BMC1
% 3.61/1.03  
% 3.61/1.03  bmc1_current_bound:                     -1
% 3.61/1.03  bmc1_last_solved_bound:                 -1
% 3.61/1.03  bmc1_unsat_core_size:                   -1
% 3.61/1.03  bmc1_unsat_core_parents_size:           -1
% 3.61/1.03  bmc1_merge_next_fun:                    0
% 3.61/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.61/1.03  
% 3.61/1.03  ------ Instantiation
% 3.61/1.03  
% 3.61/1.03  inst_num_of_clauses:                    880
% 3.61/1.03  inst_num_in_passive:                    422
% 3.61/1.03  inst_num_in_active:                     365
% 3.61/1.03  inst_num_in_unprocessed:                92
% 3.61/1.03  inst_num_of_loops:                      468
% 3.61/1.03  inst_num_of_learning_restarts:          0
% 3.61/1.03  inst_num_moves_active_passive:          99
% 3.61/1.03  inst_lit_activity:                      0
% 3.61/1.03  inst_lit_activity_moves:                0
% 3.61/1.03  inst_num_tautologies:                   0
% 3.61/1.03  inst_num_prop_implied:                  0
% 3.61/1.03  inst_num_existing_simplified:           0
% 3.61/1.03  inst_num_eq_res_simplified:             0
% 3.61/1.03  inst_num_child_elim:                    0
% 3.61/1.03  inst_num_of_dismatching_blockings:      121
% 3.61/1.03  inst_num_of_non_proper_insts:           681
% 3.61/1.03  inst_num_of_duplicates:                 0
% 3.61/1.03  inst_inst_num_from_inst_to_res:         0
% 3.61/1.03  inst_dismatching_checking_time:         0.
% 3.61/1.03  
% 3.61/1.03  ------ Resolution
% 3.61/1.03  
% 3.61/1.03  res_num_of_clauses:                     0
% 3.61/1.03  res_num_in_passive:                     0
% 3.61/1.03  res_num_in_active:                      0
% 3.61/1.03  res_num_of_loops:                       163
% 3.61/1.03  res_forward_subset_subsumed:            54
% 3.61/1.03  res_backward_subset_subsumed:           0
% 3.61/1.03  res_forward_subsumed:                   0
% 3.61/1.03  res_backward_subsumed:                  0
% 3.61/1.03  res_forward_subsumption_resolution:     0
% 3.61/1.03  res_backward_subsumption_resolution:    0
% 3.61/1.03  res_clause_to_clause_subsumption:       674
% 3.61/1.03  res_orphan_elimination:                 0
% 3.61/1.03  res_tautology_del:                      47
% 3.61/1.03  res_num_eq_res_simplified:              0
% 3.61/1.03  res_num_sel_changes:                    0
% 3.61/1.03  res_moves_from_active_to_pass:          0
% 3.61/1.03  
% 3.61/1.03  ------ Superposition
% 3.61/1.03  
% 3.61/1.03  sup_time_total:                         0.
% 3.61/1.03  sup_time_generating:                    0.
% 3.61/1.03  sup_time_sim_full:                      0.
% 3.61/1.03  sup_time_sim_immed:                     0.
% 3.61/1.03  
% 3.61/1.03  sup_num_of_clauses:                     127
% 3.61/1.03  sup_num_in_active:                      56
% 3.61/1.03  sup_num_in_passive:                     71
% 3.61/1.03  sup_num_of_loops:                       92
% 3.61/1.03  sup_fw_superposition:                   79
% 3.61/1.03  sup_bw_superposition:                   92
% 3.61/1.03  sup_immediate_simplified:               54
% 3.61/1.03  sup_given_eliminated:                   2
% 3.61/1.03  comparisons_done:                       0
% 3.61/1.03  comparisons_avoided:                    28
% 3.61/1.03  
% 3.61/1.03  ------ Simplifications
% 3.61/1.03  
% 3.61/1.03  
% 3.61/1.03  sim_fw_subset_subsumed:                 20
% 3.61/1.03  sim_bw_subset_subsumed:                 9
% 3.61/1.03  sim_fw_subsumed:                        4
% 3.61/1.03  sim_bw_subsumed:                        0
% 3.61/1.03  sim_fw_subsumption_res:                 4
% 3.61/1.03  sim_bw_subsumption_res:                 0
% 3.61/1.03  sim_tautology_del:                      12
% 3.61/1.03  sim_eq_tautology_del:                   14
% 3.61/1.03  sim_eq_res_simp:                        3
% 3.61/1.03  sim_fw_demodulated:                     25
% 3.61/1.03  sim_bw_demodulated:                     34
% 3.61/1.03  sim_light_normalised:                   5
% 3.61/1.03  sim_joinable_taut:                      0
% 3.61/1.03  sim_joinable_simp:                      0
% 3.61/1.03  sim_ac_normalised:                      0
% 3.61/1.03  sim_smt_subsumption:                    0
% 3.61/1.03  
%------------------------------------------------------------------------------
