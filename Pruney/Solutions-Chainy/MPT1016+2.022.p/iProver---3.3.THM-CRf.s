%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:55 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  161 (9871 expanded)
%              Number of clauses        :  101 (2763 expanded)
%              Number of leaves         :   13 (1968 expanded)
%              Depth                    :   33
%              Number of atoms          :  607 (72987 expanded)
%              Number of equality atoms :  296 (24405 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f38,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f43,f42])).

fof(f74,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f59,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_948,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_950,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_33])).

cnf(c_2986,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2992,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4014,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2986,c_2992])).

cnf(c_4179,plain,
    ( k1_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_950,c_4014])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_505,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_506,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_2979,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_4183,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_2979])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_544,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_545,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_546,plain,
    ( sK1(sK3) != sK0(sK3)
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3803,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2986,c_2994])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_257])).

cnf(c_2985,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_3879,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3803,c_2985])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2993,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3888,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3879,c_2993])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_531,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_532,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_2977,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_3890,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_2977])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4056,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4057,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4056])).

cnf(c_15,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_518,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_519,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_2978,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_4184,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_2978])).

cnf(c_4604,plain,
    ( v2_funct_1(sK3) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4183,c_546,c_3888,c_3890,c_4057,c_4184])).

cnf(c_4605,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4604])).

cnf(c_29,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2990,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4611,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4605,c_2990])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_481,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_2332,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_482])).

cnf(c_2981,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2332])).

cnf(c_4777,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK2 = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4611,c_2981])).

cnf(c_2333,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_482])).

cnf(c_2980,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2333])).

cnf(c_4610,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_2980])).

cnf(c_5346,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK5 = X0
    | sK2 = k1_xboole_0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4777,c_3888,c_4610])).

cnf(c_5347,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK2 = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5346])).

cnf(c_5359,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5347])).

cnf(c_28,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4944,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_4945,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK4)
    | sK4 = sK5
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4944])).

cnf(c_5512,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5359,c_45,c_3888,c_4605,c_4610,c_4611,c_4945])).

cnf(c_5519,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,sK2) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_5512])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5608,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5519,c_43,c_4605])).

cnf(c_5614,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_5608])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5665,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5614,c_42,c_4605])).

cnf(c_5673,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5665,c_4014])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_935,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_934])).

cnf(c_2973,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3099,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2973,c_7])).

cnf(c_5675,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5665,c_3099])).

cnf(c_5692,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5675])).

cnf(c_5680,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5665,c_2986])).

cnf(c_5682,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5680,c_7])).

cnf(c_5695,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5692,c_5682])).

cnf(c_5700,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5673,c_5695])).

cnf(c_5873,plain,
    ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5700,c_2979])).

cnf(c_2989,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5678,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5665,c_2989])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_2984,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_5719,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5678,c_2984])).

cnf(c_6014,plain,
    ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5873,c_3888,c_5719])).

cnf(c_6019,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6014,c_2984])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.89/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/1.01  
% 2.89/1.01  ------  iProver source info
% 2.89/1.01  
% 2.89/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.89/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/1.01  git: non_committed_changes: false
% 2.89/1.01  git: last_make_outside_of_git: false
% 2.89/1.01  
% 2.89/1.01  ------ 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options
% 2.89/1.01  
% 2.89/1.01  --out_options                           all
% 2.89/1.01  --tptp_safe_out                         true
% 2.89/1.01  --problem_path                          ""
% 2.89/1.01  --include_path                          ""
% 2.89/1.01  --clausifier                            res/vclausify_rel
% 2.89/1.01  --clausifier_options                    --mode clausify
% 2.89/1.01  --stdin                                 false
% 2.89/1.01  --stats_out                             all
% 2.89/1.01  
% 2.89/1.01  ------ General Options
% 2.89/1.01  
% 2.89/1.01  --fof                                   false
% 2.89/1.01  --time_out_real                         305.
% 2.89/1.01  --time_out_virtual                      -1.
% 2.89/1.01  --symbol_type_check                     false
% 2.89/1.01  --clausify_out                          false
% 2.89/1.01  --sig_cnt_out                           false
% 2.89/1.01  --trig_cnt_out                          false
% 2.89/1.01  --trig_cnt_out_tolerance                1.
% 2.89/1.01  --trig_cnt_out_sk_spl                   false
% 2.89/1.01  --abstr_cl_out                          false
% 2.89/1.01  
% 2.89/1.01  ------ Global Options
% 2.89/1.01  
% 2.89/1.01  --schedule                              default
% 2.89/1.01  --add_important_lit                     false
% 2.89/1.01  --prop_solver_per_cl                    1000
% 2.89/1.01  --min_unsat_core                        false
% 2.89/1.01  --soft_assumptions                      false
% 2.89/1.01  --soft_lemma_size                       3
% 2.89/1.01  --prop_impl_unit_size                   0
% 2.89/1.01  --prop_impl_unit                        []
% 2.89/1.01  --share_sel_clauses                     true
% 2.89/1.01  --reset_solvers                         false
% 2.89/1.01  --bc_imp_inh                            [conj_cone]
% 2.89/1.01  --conj_cone_tolerance                   3.
% 2.89/1.01  --extra_neg_conj                        none
% 2.89/1.01  --large_theory_mode                     true
% 2.89/1.01  --prolific_symb_bound                   200
% 2.89/1.01  --lt_threshold                          2000
% 2.89/1.01  --clause_weak_htbl                      true
% 2.89/1.01  --gc_record_bc_elim                     false
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing Options
% 2.89/1.01  
% 2.89/1.01  --preprocessing_flag                    true
% 2.89/1.01  --time_out_prep_mult                    0.1
% 2.89/1.01  --splitting_mode                        input
% 2.89/1.01  --splitting_grd                         true
% 2.89/1.01  --splitting_cvd                         false
% 2.89/1.01  --splitting_cvd_svl                     false
% 2.89/1.01  --splitting_nvd                         32
% 2.89/1.01  --sub_typing                            true
% 2.89/1.01  --prep_gs_sim                           true
% 2.89/1.01  --prep_unflatten                        true
% 2.89/1.01  --prep_res_sim                          true
% 2.89/1.01  --prep_upred                            true
% 2.89/1.01  --prep_sem_filter                       exhaustive
% 2.89/1.01  --prep_sem_filter_out                   false
% 2.89/1.01  --pred_elim                             true
% 2.89/1.01  --res_sim_input                         true
% 2.89/1.01  --eq_ax_congr_red                       true
% 2.89/1.01  --pure_diseq_elim                       true
% 2.89/1.01  --brand_transform                       false
% 2.89/1.01  --non_eq_to_eq                          false
% 2.89/1.01  --prep_def_merge                        true
% 2.89/1.01  --prep_def_merge_prop_impl              false
% 2.89/1.01  --prep_def_merge_mbd                    true
% 2.89/1.01  --prep_def_merge_tr_red                 false
% 2.89/1.01  --prep_def_merge_tr_cl                  false
% 2.89/1.01  --smt_preprocessing                     true
% 2.89/1.01  --smt_ac_axioms                         fast
% 2.89/1.01  --preprocessed_out                      false
% 2.89/1.01  --preprocessed_stats                    false
% 2.89/1.01  
% 2.89/1.01  ------ Abstraction refinement Options
% 2.89/1.01  
% 2.89/1.01  --abstr_ref                             []
% 2.89/1.01  --abstr_ref_prep                        false
% 2.89/1.01  --abstr_ref_until_sat                   false
% 2.89/1.01  --abstr_ref_sig_restrict                funpre
% 2.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.01  --abstr_ref_under                       []
% 2.89/1.01  
% 2.89/1.01  ------ SAT Options
% 2.89/1.01  
% 2.89/1.01  --sat_mode                              false
% 2.89/1.01  --sat_fm_restart_options                ""
% 2.89/1.01  --sat_gr_def                            false
% 2.89/1.01  --sat_epr_types                         true
% 2.89/1.01  --sat_non_cyclic_types                  false
% 2.89/1.01  --sat_finite_models                     false
% 2.89/1.01  --sat_fm_lemmas                         false
% 2.89/1.01  --sat_fm_prep                           false
% 2.89/1.01  --sat_fm_uc_incr                        true
% 2.89/1.01  --sat_out_model                         small
% 2.89/1.01  --sat_out_clauses                       false
% 2.89/1.01  
% 2.89/1.01  ------ QBF Options
% 2.89/1.01  
% 2.89/1.01  --qbf_mode                              false
% 2.89/1.01  --qbf_elim_univ                         false
% 2.89/1.01  --qbf_dom_inst                          none
% 2.89/1.01  --qbf_dom_pre_inst                      false
% 2.89/1.01  --qbf_sk_in                             false
% 2.89/1.01  --qbf_pred_elim                         true
% 2.89/1.01  --qbf_split                             512
% 2.89/1.01  
% 2.89/1.01  ------ BMC1 Options
% 2.89/1.01  
% 2.89/1.01  --bmc1_incremental                      false
% 2.89/1.01  --bmc1_axioms                           reachable_all
% 2.89/1.01  --bmc1_min_bound                        0
% 2.89/1.01  --bmc1_max_bound                        -1
% 2.89/1.01  --bmc1_max_bound_default                -1
% 2.89/1.01  --bmc1_symbol_reachability              true
% 2.89/1.01  --bmc1_property_lemmas                  false
% 2.89/1.01  --bmc1_k_induction                      false
% 2.89/1.01  --bmc1_non_equiv_states                 false
% 2.89/1.01  --bmc1_deadlock                         false
% 2.89/1.01  --bmc1_ucm                              false
% 2.89/1.01  --bmc1_add_unsat_core                   none
% 2.89/1.01  --bmc1_unsat_core_children              false
% 2.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.01  --bmc1_out_stat                         full
% 2.89/1.01  --bmc1_ground_init                      false
% 2.89/1.01  --bmc1_pre_inst_next_state              false
% 2.89/1.01  --bmc1_pre_inst_state                   false
% 2.89/1.01  --bmc1_pre_inst_reach_state             false
% 2.89/1.01  --bmc1_out_unsat_core                   false
% 2.89/1.01  --bmc1_aig_witness_out                  false
% 2.89/1.01  --bmc1_verbose                          false
% 2.89/1.01  --bmc1_dump_clauses_tptp                false
% 2.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.01  --bmc1_dump_file                        -
% 2.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.01  --bmc1_ucm_extend_mode                  1
% 2.89/1.01  --bmc1_ucm_init_mode                    2
% 2.89/1.01  --bmc1_ucm_cone_mode                    none
% 2.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.01  --bmc1_ucm_relax_model                  4
% 2.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.01  --bmc1_ucm_layered_model                none
% 2.89/1.01  --bmc1_ucm_max_lemma_size               10
% 2.89/1.01  
% 2.89/1.01  ------ AIG Options
% 2.89/1.01  
% 2.89/1.01  --aig_mode                              false
% 2.89/1.01  
% 2.89/1.01  ------ Instantiation Options
% 2.89/1.01  
% 2.89/1.01  --instantiation_flag                    true
% 2.89/1.01  --inst_sos_flag                         false
% 2.89/1.01  --inst_sos_phase                        true
% 2.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel_side                     num_symb
% 2.89/1.01  --inst_solver_per_active                1400
% 2.89/1.01  --inst_solver_calls_frac                1.
% 2.89/1.01  --inst_passive_queue_type               priority_queues
% 2.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.01  --inst_passive_queues_freq              [25;2]
% 2.89/1.01  --inst_dismatching                      true
% 2.89/1.01  --inst_eager_unprocessed_to_passive     true
% 2.89/1.01  --inst_prop_sim_given                   true
% 2.89/1.01  --inst_prop_sim_new                     false
% 2.89/1.01  --inst_subs_new                         false
% 2.89/1.01  --inst_eq_res_simp                      false
% 2.89/1.01  --inst_subs_given                       false
% 2.89/1.01  --inst_orphan_elimination               true
% 2.89/1.01  --inst_learning_loop_flag               true
% 2.89/1.01  --inst_learning_start                   3000
% 2.89/1.01  --inst_learning_factor                  2
% 2.89/1.01  --inst_start_prop_sim_after_learn       3
% 2.89/1.01  --inst_sel_renew                        solver
% 2.89/1.01  --inst_lit_activity_flag                true
% 2.89/1.01  --inst_restr_to_given                   false
% 2.89/1.01  --inst_activity_threshold               500
% 2.89/1.01  --inst_out_proof                        true
% 2.89/1.01  
% 2.89/1.01  ------ Resolution Options
% 2.89/1.01  
% 2.89/1.01  --resolution_flag                       true
% 2.89/1.01  --res_lit_sel                           adaptive
% 2.89/1.01  --res_lit_sel_side                      none
% 2.89/1.01  --res_ordering                          kbo
% 2.89/1.01  --res_to_prop_solver                    active
% 2.89/1.01  --res_prop_simpl_new                    false
% 2.89/1.01  --res_prop_simpl_given                  true
% 2.89/1.01  --res_passive_queue_type                priority_queues
% 2.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.01  --res_passive_queues_freq               [15;5]
% 2.89/1.01  --res_forward_subs                      full
% 2.89/1.01  --res_backward_subs                     full
% 2.89/1.01  --res_forward_subs_resolution           true
% 2.89/1.01  --res_backward_subs_resolution          true
% 2.89/1.01  --res_orphan_elimination                true
% 2.89/1.01  --res_time_limit                        2.
% 2.89/1.01  --res_out_proof                         true
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Options
% 2.89/1.01  
% 2.89/1.01  --superposition_flag                    true
% 2.89/1.01  --sup_passive_queue_type                priority_queues
% 2.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.01  --demod_completeness_check              fast
% 2.89/1.01  --demod_use_ground                      true
% 2.89/1.01  --sup_to_prop_solver                    passive
% 2.89/1.01  --sup_prop_simpl_new                    true
% 2.89/1.01  --sup_prop_simpl_given                  true
% 2.89/1.01  --sup_fun_splitting                     false
% 2.89/1.01  --sup_smt_interval                      50000
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Simplification Setup
% 2.89/1.01  
% 2.89/1.01  --sup_indices_passive                   []
% 2.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_full_bw                           [BwDemod]
% 2.89/1.01  --sup_immed_triv                        [TrivRules]
% 2.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_immed_bw_main                     []
% 2.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  
% 2.89/1.01  ------ Combination Options
% 2.89/1.01  
% 2.89/1.01  --comb_res_mult                         3
% 2.89/1.01  --comb_sup_mult                         2
% 2.89/1.01  --comb_inst_mult                        10
% 2.89/1.01  
% 2.89/1.01  ------ Debug Options
% 2.89/1.01  
% 2.89/1.01  --dbg_backtrace                         false
% 2.89/1.01  --dbg_dump_prop_clauses                 false
% 2.89/1.01  --dbg_dump_prop_clauses_file            -
% 2.89/1.01  --dbg_out_stat                          false
% 2.89/1.01  ------ Parsing...
% 2.89/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/1.01  ------ Proving...
% 2.89/1.01  ------ Problem Properties 
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  clauses                                 30
% 2.89/1.01  conjectures                             6
% 2.89/1.01  EPR                                     9
% 2.89/1.01  Horn                                    23
% 2.89/1.01  unary                                   7
% 2.89/1.01  binary                                  8
% 2.89/1.01  lits                                    73
% 2.89/1.01  lits eq                                 23
% 2.89/1.01  fd_pure                                 0
% 2.89/1.01  fd_pseudo                               0
% 2.89/1.01  fd_cond                                 1
% 2.89/1.01  fd_pseudo_cond                          4
% 2.89/1.01  AC symbols                              0
% 2.89/1.01  
% 2.89/1.01  ------ Schedule dynamic 5 is on 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  ------ 
% 2.89/1.01  Current options:
% 2.89/1.01  ------ 
% 2.89/1.01  
% 2.89/1.01  ------ Input Options
% 2.89/1.01  
% 2.89/1.01  --out_options                           all
% 2.89/1.01  --tptp_safe_out                         true
% 2.89/1.01  --problem_path                          ""
% 2.89/1.01  --include_path                          ""
% 2.89/1.01  --clausifier                            res/vclausify_rel
% 2.89/1.01  --clausifier_options                    --mode clausify
% 2.89/1.01  --stdin                                 false
% 2.89/1.01  --stats_out                             all
% 2.89/1.01  
% 2.89/1.01  ------ General Options
% 2.89/1.01  
% 2.89/1.01  --fof                                   false
% 2.89/1.01  --time_out_real                         305.
% 2.89/1.01  --time_out_virtual                      -1.
% 2.89/1.01  --symbol_type_check                     false
% 2.89/1.01  --clausify_out                          false
% 2.89/1.01  --sig_cnt_out                           false
% 2.89/1.01  --trig_cnt_out                          false
% 2.89/1.01  --trig_cnt_out_tolerance                1.
% 2.89/1.01  --trig_cnt_out_sk_spl                   false
% 2.89/1.01  --abstr_cl_out                          false
% 2.89/1.01  
% 2.89/1.01  ------ Global Options
% 2.89/1.01  
% 2.89/1.01  --schedule                              default
% 2.89/1.01  --add_important_lit                     false
% 2.89/1.01  --prop_solver_per_cl                    1000
% 2.89/1.01  --min_unsat_core                        false
% 2.89/1.01  --soft_assumptions                      false
% 2.89/1.01  --soft_lemma_size                       3
% 2.89/1.01  --prop_impl_unit_size                   0
% 2.89/1.01  --prop_impl_unit                        []
% 2.89/1.01  --share_sel_clauses                     true
% 2.89/1.01  --reset_solvers                         false
% 2.89/1.01  --bc_imp_inh                            [conj_cone]
% 2.89/1.01  --conj_cone_tolerance                   3.
% 2.89/1.01  --extra_neg_conj                        none
% 2.89/1.01  --large_theory_mode                     true
% 2.89/1.01  --prolific_symb_bound                   200
% 2.89/1.01  --lt_threshold                          2000
% 2.89/1.01  --clause_weak_htbl                      true
% 2.89/1.01  --gc_record_bc_elim                     false
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing Options
% 2.89/1.01  
% 2.89/1.01  --preprocessing_flag                    true
% 2.89/1.01  --time_out_prep_mult                    0.1
% 2.89/1.01  --splitting_mode                        input
% 2.89/1.01  --splitting_grd                         true
% 2.89/1.01  --splitting_cvd                         false
% 2.89/1.01  --splitting_cvd_svl                     false
% 2.89/1.01  --splitting_nvd                         32
% 2.89/1.01  --sub_typing                            true
% 2.89/1.01  --prep_gs_sim                           true
% 2.89/1.01  --prep_unflatten                        true
% 2.89/1.01  --prep_res_sim                          true
% 2.89/1.01  --prep_upred                            true
% 2.89/1.01  --prep_sem_filter                       exhaustive
% 2.89/1.01  --prep_sem_filter_out                   false
% 2.89/1.01  --pred_elim                             true
% 2.89/1.01  --res_sim_input                         true
% 2.89/1.01  --eq_ax_congr_red                       true
% 2.89/1.01  --pure_diseq_elim                       true
% 2.89/1.01  --brand_transform                       false
% 2.89/1.01  --non_eq_to_eq                          false
% 2.89/1.01  --prep_def_merge                        true
% 2.89/1.01  --prep_def_merge_prop_impl              false
% 2.89/1.01  --prep_def_merge_mbd                    true
% 2.89/1.01  --prep_def_merge_tr_red                 false
% 2.89/1.01  --prep_def_merge_tr_cl                  false
% 2.89/1.01  --smt_preprocessing                     true
% 2.89/1.01  --smt_ac_axioms                         fast
% 2.89/1.01  --preprocessed_out                      false
% 2.89/1.01  --preprocessed_stats                    false
% 2.89/1.01  
% 2.89/1.01  ------ Abstraction refinement Options
% 2.89/1.01  
% 2.89/1.01  --abstr_ref                             []
% 2.89/1.01  --abstr_ref_prep                        false
% 2.89/1.01  --abstr_ref_until_sat                   false
% 2.89/1.01  --abstr_ref_sig_restrict                funpre
% 2.89/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.01  --abstr_ref_under                       []
% 2.89/1.01  
% 2.89/1.01  ------ SAT Options
% 2.89/1.01  
% 2.89/1.01  --sat_mode                              false
% 2.89/1.01  --sat_fm_restart_options                ""
% 2.89/1.01  --sat_gr_def                            false
% 2.89/1.01  --sat_epr_types                         true
% 2.89/1.01  --sat_non_cyclic_types                  false
% 2.89/1.01  --sat_finite_models                     false
% 2.89/1.01  --sat_fm_lemmas                         false
% 2.89/1.01  --sat_fm_prep                           false
% 2.89/1.01  --sat_fm_uc_incr                        true
% 2.89/1.01  --sat_out_model                         small
% 2.89/1.01  --sat_out_clauses                       false
% 2.89/1.01  
% 2.89/1.01  ------ QBF Options
% 2.89/1.01  
% 2.89/1.01  --qbf_mode                              false
% 2.89/1.01  --qbf_elim_univ                         false
% 2.89/1.01  --qbf_dom_inst                          none
% 2.89/1.01  --qbf_dom_pre_inst                      false
% 2.89/1.01  --qbf_sk_in                             false
% 2.89/1.01  --qbf_pred_elim                         true
% 2.89/1.01  --qbf_split                             512
% 2.89/1.01  
% 2.89/1.01  ------ BMC1 Options
% 2.89/1.01  
% 2.89/1.01  --bmc1_incremental                      false
% 2.89/1.01  --bmc1_axioms                           reachable_all
% 2.89/1.01  --bmc1_min_bound                        0
% 2.89/1.01  --bmc1_max_bound                        -1
% 2.89/1.01  --bmc1_max_bound_default                -1
% 2.89/1.01  --bmc1_symbol_reachability              true
% 2.89/1.01  --bmc1_property_lemmas                  false
% 2.89/1.01  --bmc1_k_induction                      false
% 2.89/1.01  --bmc1_non_equiv_states                 false
% 2.89/1.01  --bmc1_deadlock                         false
% 2.89/1.01  --bmc1_ucm                              false
% 2.89/1.01  --bmc1_add_unsat_core                   none
% 2.89/1.01  --bmc1_unsat_core_children              false
% 2.89/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.01  --bmc1_out_stat                         full
% 2.89/1.01  --bmc1_ground_init                      false
% 2.89/1.01  --bmc1_pre_inst_next_state              false
% 2.89/1.01  --bmc1_pre_inst_state                   false
% 2.89/1.01  --bmc1_pre_inst_reach_state             false
% 2.89/1.01  --bmc1_out_unsat_core                   false
% 2.89/1.01  --bmc1_aig_witness_out                  false
% 2.89/1.01  --bmc1_verbose                          false
% 2.89/1.01  --bmc1_dump_clauses_tptp                false
% 2.89/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.01  --bmc1_dump_file                        -
% 2.89/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.01  --bmc1_ucm_extend_mode                  1
% 2.89/1.01  --bmc1_ucm_init_mode                    2
% 2.89/1.01  --bmc1_ucm_cone_mode                    none
% 2.89/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.01  --bmc1_ucm_relax_model                  4
% 2.89/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.01  --bmc1_ucm_layered_model                none
% 2.89/1.01  --bmc1_ucm_max_lemma_size               10
% 2.89/1.01  
% 2.89/1.01  ------ AIG Options
% 2.89/1.01  
% 2.89/1.01  --aig_mode                              false
% 2.89/1.01  
% 2.89/1.01  ------ Instantiation Options
% 2.89/1.01  
% 2.89/1.01  --instantiation_flag                    true
% 2.89/1.01  --inst_sos_flag                         false
% 2.89/1.01  --inst_sos_phase                        true
% 2.89/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.01  --inst_lit_sel_side                     none
% 2.89/1.01  --inst_solver_per_active                1400
% 2.89/1.01  --inst_solver_calls_frac                1.
% 2.89/1.01  --inst_passive_queue_type               priority_queues
% 2.89/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.01  --inst_passive_queues_freq              [25;2]
% 2.89/1.01  --inst_dismatching                      true
% 2.89/1.01  --inst_eager_unprocessed_to_passive     true
% 2.89/1.01  --inst_prop_sim_given                   true
% 2.89/1.01  --inst_prop_sim_new                     false
% 2.89/1.01  --inst_subs_new                         false
% 2.89/1.01  --inst_eq_res_simp                      false
% 2.89/1.01  --inst_subs_given                       false
% 2.89/1.01  --inst_orphan_elimination               true
% 2.89/1.01  --inst_learning_loop_flag               true
% 2.89/1.01  --inst_learning_start                   3000
% 2.89/1.01  --inst_learning_factor                  2
% 2.89/1.01  --inst_start_prop_sim_after_learn       3
% 2.89/1.01  --inst_sel_renew                        solver
% 2.89/1.01  --inst_lit_activity_flag                true
% 2.89/1.01  --inst_restr_to_given                   false
% 2.89/1.01  --inst_activity_threshold               500
% 2.89/1.01  --inst_out_proof                        true
% 2.89/1.01  
% 2.89/1.01  ------ Resolution Options
% 2.89/1.01  
% 2.89/1.01  --resolution_flag                       false
% 2.89/1.01  --res_lit_sel                           adaptive
% 2.89/1.01  --res_lit_sel_side                      none
% 2.89/1.01  --res_ordering                          kbo
% 2.89/1.01  --res_to_prop_solver                    active
% 2.89/1.01  --res_prop_simpl_new                    false
% 2.89/1.01  --res_prop_simpl_given                  true
% 2.89/1.01  --res_passive_queue_type                priority_queues
% 2.89/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.01  --res_passive_queues_freq               [15;5]
% 2.89/1.01  --res_forward_subs                      full
% 2.89/1.01  --res_backward_subs                     full
% 2.89/1.01  --res_forward_subs_resolution           true
% 2.89/1.01  --res_backward_subs_resolution          true
% 2.89/1.01  --res_orphan_elimination                true
% 2.89/1.01  --res_time_limit                        2.
% 2.89/1.01  --res_out_proof                         true
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Options
% 2.89/1.01  
% 2.89/1.01  --superposition_flag                    true
% 2.89/1.01  --sup_passive_queue_type                priority_queues
% 2.89/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.01  --demod_completeness_check              fast
% 2.89/1.01  --demod_use_ground                      true
% 2.89/1.01  --sup_to_prop_solver                    passive
% 2.89/1.01  --sup_prop_simpl_new                    true
% 2.89/1.01  --sup_prop_simpl_given                  true
% 2.89/1.01  --sup_fun_splitting                     false
% 2.89/1.01  --sup_smt_interval                      50000
% 2.89/1.01  
% 2.89/1.01  ------ Superposition Simplification Setup
% 2.89/1.01  
% 2.89/1.01  --sup_indices_passive                   []
% 2.89/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_full_bw                           [BwDemod]
% 2.89/1.01  --sup_immed_triv                        [TrivRules]
% 2.89/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_immed_bw_main                     []
% 2.89/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.01  
% 2.89/1.01  ------ Combination Options
% 2.89/1.01  
% 2.89/1.01  --comb_res_mult                         3
% 2.89/1.01  --comb_sup_mult                         2
% 2.89/1.01  --comb_inst_mult                        10
% 2.89/1.01  
% 2.89/1.01  ------ Debug Options
% 2.89/1.01  
% 2.89/1.01  --dbg_backtrace                         false
% 2.89/1.01  --dbg_dump_prop_clauses                 false
% 2.89/1.01  --dbg_dump_prop_clauses_file            -
% 2.89/1.01  --dbg_out_stat                          false
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  ------ Proving...
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  % SZS status Theorem for theBenchmark.p
% 2.89/1.01  
% 2.89/1.01   Resolution empty clause
% 2.89/1.01  
% 2.89/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  fof(f12,axiom,(
% 2.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f23,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(ennf_transformation,[],[f12])).
% 2.89/1.01  
% 2.89/1.01  fof(f24,plain,(
% 2.89/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(flattening,[],[f23])).
% 2.89/1.01  
% 2.89/1.01  fof(f38,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(nnf_transformation,[],[f24])).
% 2.89/1.01  
% 2.89/1.01  fof(f67,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f38])).
% 2.89/1.01  
% 2.89/1.01  fof(f13,conjecture,(
% 2.89/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f14,negated_conjecture,(
% 2.89/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.89/1.01    inference(negated_conjecture,[],[f13])).
% 2.89/1.01  
% 2.89/1.01  fof(f25,plain,(
% 2.89/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.89/1.01    inference(ennf_transformation,[],[f14])).
% 2.89/1.01  
% 2.89/1.01  fof(f26,plain,(
% 2.89/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.89/1.01    inference(flattening,[],[f25])).
% 2.89/1.01  
% 2.89/1.01  fof(f39,plain,(
% 2.89/1.01    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.89/1.01    inference(nnf_transformation,[],[f26])).
% 2.89/1.01  
% 2.89/1.01  fof(f40,plain,(
% 2.89/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.89/1.01    inference(flattening,[],[f39])).
% 2.89/1.01  
% 2.89/1.01  fof(f41,plain,(
% 2.89/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.89/1.01    inference(rectify,[],[f40])).
% 2.89/1.01  
% 2.89/1.01  fof(f43,plain,(
% 2.89/1.01    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.89/1.01    introduced(choice_axiom,[])).
% 2.89/1.01  
% 2.89/1.01  fof(f42,plain,(
% 2.89/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.89/1.01    introduced(choice_axiom,[])).
% 2.89/1.01  
% 2.89/1.01  fof(f44,plain,(
% 2.89/1.01    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f43,f42])).
% 2.89/1.01  
% 2.89/1.01  fof(f74,plain,(
% 2.89/1.01    v1_funct_2(sK3,sK2,sK2)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f75,plain,(
% 2.89/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f11,axiom,(
% 2.89/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f22,plain,(
% 2.89/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/1.01    inference(ennf_transformation,[],[f11])).
% 2.89/1.01  
% 2.89/1.01  fof(f66,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f22])).
% 2.89/1.01  
% 2.89/1.01  fof(f9,axiom,(
% 2.89/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f18,plain,(
% 2.89/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.89/1.01    inference(ennf_transformation,[],[f9])).
% 2.89/1.01  
% 2.89/1.01  fof(f19,plain,(
% 2.89/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(flattening,[],[f18])).
% 2.89/1.01  
% 2.89/1.01  fof(f32,plain,(
% 2.89/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(nnf_transformation,[],[f19])).
% 2.89/1.01  
% 2.89/1.01  fof(f33,plain,(
% 2.89/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(rectify,[],[f32])).
% 2.89/1.01  
% 2.89/1.01  fof(f34,plain,(
% 2.89/1.01    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.89/1.01    introduced(choice_axiom,[])).
% 2.89/1.01  
% 2.89/1.01  fof(f35,plain,(
% 2.89/1.01    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 2.89/1.01  
% 2.89/1.01  fof(f59,plain,(
% 2.89/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f73,plain,(
% 2.89/1.01    v1_funct_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f62,plain,(
% 2.89/1.01    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f6,axiom,(
% 2.89/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f31,plain,(
% 2.89/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.89/1.01    inference(nnf_transformation,[],[f6])).
% 2.89/1.01  
% 2.89/1.01  fof(f54,plain,(
% 2.89/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f31])).
% 2.89/1.01  
% 2.89/1.01  fof(f7,axiom,(
% 2.89/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f17,plain,(
% 2.89/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.89/1.01    inference(ennf_transformation,[],[f7])).
% 2.89/1.01  
% 2.89/1.01  fof(f56,plain,(
% 2.89/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f17])).
% 2.89/1.01  
% 2.89/1.01  fof(f55,plain,(
% 2.89/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f31])).
% 2.89/1.01  
% 2.89/1.01  fof(f8,axiom,(
% 2.89/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f57,plain,(
% 2.89/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f8])).
% 2.89/1.01  
% 2.89/1.01  fof(f61,plain,(
% 2.89/1.01    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f76,plain,(
% 2.89/1.01    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f60,plain,(
% 2.89/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f79,plain,(
% 2.89/1.01    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f58,plain,(
% 2.89/1.01    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f35])).
% 2.89/1.01  
% 2.89/1.01  fof(f80,plain,(
% 2.89/1.01    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f78,plain,(
% 2.89/1.01    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f77,plain,(
% 2.89/1.01    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.89/1.01    inference(cnf_transformation,[],[f44])).
% 2.89/1.01  
% 2.89/1.01  fof(f68,plain,(
% 2.89/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/1.01    inference(cnf_transformation,[],[f38])).
% 2.89/1.01  
% 2.89/1.01  fof(f90,plain,(
% 2.89/1.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.89/1.01    inference(equality_resolution,[],[f68])).
% 2.89/1.01  
% 2.89/1.01  fof(f5,axiom,(
% 2.89/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f29,plain,(
% 2.89/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/1.01    inference(nnf_transformation,[],[f5])).
% 2.89/1.01  
% 2.89/1.01  fof(f30,plain,(
% 2.89/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/1.01    inference(flattening,[],[f29])).
% 2.89/1.01  
% 2.89/1.01  fof(f52,plain,(
% 2.89/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.89/1.01    inference(cnf_transformation,[],[f30])).
% 2.89/1.01  
% 2.89/1.01  fof(f84,plain,(
% 2.89/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.89/1.01    inference(equality_resolution,[],[f52])).
% 2.89/1.01  
% 2.89/1.01  fof(f1,axiom,(
% 2.89/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f15,plain,(
% 2.89/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.89/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 2.89/1.01  
% 2.89/1.01  fof(f16,plain,(
% 2.89/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.89/1.01    inference(ennf_transformation,[],[f15])).
% 2.89/1.01  
% 2.89/1.01  fof(f45,plain,(
% 2.89/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.89/1.01    inference(cnf_transformation,[],[f16])).
% 2.89/1.01  
% 2.89/1.01  fof(f2,axiom,(
% 2.89/1.01    v1_xboole_0(k1_xboole_0)),
% 2.89/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.01  
% 2.89/1.01  fof(f46,plain,(
% 2.89/1.01    v1_xboole_0(k1_xboole_0)),
% 2.89/1.01    inference(cnf_transformation,[],[f2])).
% 2.89/1.01  
% 2.89/1.01  cnf(c_27,plain,
% 2.89/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_34,negated_conjecture,
% 2.89/1.01      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.89/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_947,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.89/1.01      | sK2 != X1
% 2.89/1.01      | sK2 != X2
% 2.89/1.01      | sK3 != X0
% 2.89/1.01      | k1_xboole_0 = X2 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_948,plain,
% 2.89/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.89/1.01      | k1_relset_1(sK2,sK2,sK3) = sK2
% 2.89/1.01      | k1_xboole_0 = sK2 ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_947]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_33,negated_conjecture,
% 2.89/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.89/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_950,plain,
% 2.89/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 2.89/1.01      inference(global_propositional_subsumption,[status(thm)],[c_948,c_33]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2986,plain,
% 2.89/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_21,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2992,plain,
% 2.89/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.89/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4014,plain,
% 2.89/1.01      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_2986,c_2992]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4179,plain,
% 2.89/1.01      ( k1_relat_1(sK3) = sK2 | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_950,c_4014]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_16,plain,
% 2.89/1.01      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.89/1.01      | ~ v1_funct_1(X0)
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_35,negated_conjecture,
% 2.89/1.01      ( v1_funct_1(sK3) ),
% 2.89/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_505,plain,
% 2.89/1.01      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0)
% 2.89/1.01      | sK3 != X0 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_506,plain,
% 2.89/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.89/1.01      | v2_funct_1(sK3)
% 2.89/1.01      | ~ v1_relat_1(sK3) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_505]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2979,plain,
% 2.89/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4183,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r2_hidden(sK0(sK3),sK2) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4179,c_2979]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_13,plain,
% 2.89/1.01      ( ~ v1_funct_1(X0)
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0)
% 2.89/1.01      | sK1(X0) != sK0(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_544,plain,
% 2.89/1.01      ( v2_funct_1(X0) | ~ v1_relat_1(X0) | sK1(X0) != sK0(X0) | sK3 != X0 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_545,plain,
% 2.89/1.01      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_544]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_546,plain,
% 2.89/1.01      ( sK1(sK3) != sK0(sK3)
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_10,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.89/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2994,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.89/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3803,plain,
% 2.89/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_2986,c_2994]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_11,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_9,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.89/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_256,plain,
% 2.89/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.89/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_257,plain,
% 2.89/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.89/1.01      inference(renaming,[status(thm)],[c_256]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_327,plain,
% 2.89/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.89/1.01      inference(bin_hyper_res,[status(thm)],[c_11,c_257]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2985,plain,
% 2.89/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.89/1.01      | v1_relat_1(X1) != iProver_top
% 2.89/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3879,plain,
% 2.89/1.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 2.89/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3803,c_2985]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_12,plain,
% 2.89/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.89/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2993,plain,
% 2.89/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3888,plain,
% 2.89/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3879,c_2993]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_14,plain,
% 2.89/1.01      ( ~ v1_funct_1(X0)
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0)
% 2.89/1.01      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.89/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_531,plain,
% 2.89/1.01      ( v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0)
% 2.89/1.01      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
% 2.89/1.01      | sK3 != X0 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_532,plain,
% 2.89/1.01      ( v2_funct_1(sK3)
% 2.89/1.01      | ~ v1_relat_1(sK3)
% 2.89/1.01      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_531]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2977,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3890,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_3888,c_2977]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_32,negated_conjecture,
% 2.89/1.01      ( ~ r2_hidden(X0,sK2)
% 2.89/1.01      | ~ r2_hidden(X1,sK2)
% 2.89/1.01      | v2_funct_1(sK3)
% 2.89/1.01      | X1 = X0
% 2.89/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4056,plain,
% 2.89/1.01      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.89/1.01      | ~ r2_hidden(sK0(sK3),sK2)
% 2.89/1.01      | v2_funct_1(sK3)
% 2.89/1.01      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.89/1.01      | sK1(sK3) = sK0(sK3) ),
% 2.89/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4057,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.89/1.01      | sK1(sK3) = sK0(sK3)
% 2.89/1.01      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.89/1.01      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_4056]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_15,plain,
% 2.89/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.89/1.01      | ~ v1_funct_1(X0)
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_518,plain,
% 2.89/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.89/1.01      | v2_funct_1(X0)
% 2.89/1.01      | ~ v1_relat_1(X0)
% 2.89/1.01      | sK3 != X0 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_519,plain,
% 2.89/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.89/1.01      | v2_funct_1(sK3)
% 2.89/1.01      | ~ v1_relat_1(sK3) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_518]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2978,plain,
% 2.89/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4184,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4179,c_2978]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4604,plain,
% 2.89/1.01      ( v2_funct_1(sK3) = iProver_top | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_4183,c_546,c_3888,c_3890,c_4057,c_4184]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4605,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 | v2_funct_1(sK3) = iProver_top ),
% 2.89/1.01      inference(renaming,[status(thm)],[c_4604]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_29,negated_conjecture,
% 2.89/1.01      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.89/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2990,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.89/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4611,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) | sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4605,c_2990]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_17,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.89/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.89/1.01      | ~ v1_funct_1(X1)
% 2.89/1.01      | ~ v2_funct_1(X1)
% 2.89/1.01      | ~ v1_relat_1(X1)
% 2.89/1.01      | X0 = X2
% 2.89/1.01      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.89/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_481,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.89/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.89/1.01      | ~ v2_funct_1(X1)
% 2.89/1.01      | ~ v1_relat_1(X1)
% 2.89/1.01      | X0 = X2
% 2.89/1.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.89/1.01      | sK3 != X1 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_482,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.89/1.01      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.89/1.01      | ~ v2_funct_1(sK3)
% 2.89/1.01      | ~ v1_relat_1(sK3)
% 2.89/1.01      | X0 = X1
% 2.89/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_481]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2332,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.89/1.01      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.89/1.01      | X0 = X1
% 2.89/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
% 2.89/1.01      | ~ sP0_iProver_split ),
% 2.89/1.01      inference(splitting,
% 2.89/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.89/1.01                [c_482]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2981,plain,
% 2.89/1.01      ( X0 = X1
% 2.89/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
% 2.89/1.01      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | sP0_iProver_split != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_2332]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4777,plain,
% 2.89/1.01      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.89/1.01      | sK2 = k1_xboole_0
% 2.89/1.01      | sK5 = X0
% 2.89/1.01      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | sP0_iProver_split != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4611,c_2981]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2333,plain,
% 2.89/1.01      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP0_iProver_split ),
% 2.89/1.01      inference(splitting,
% 2.89/1.01                [splitting(split),new_symbols(definition,[])],
% 2.89/1.01                [c_482]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2980,plain,
% 2.89/1.01      ( v2_funct_1(sK3) != iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top
% 2.89/1.01      | sP0_iProver_split = iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_2333]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4610,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top
% 2.89/1.01      | sP0_iProver_split = iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4605,c_2980]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5346,plain,
% 2.89/1.01      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | sK5 = X0
% 2.89/1.01      | sK2 = k1_xboole_0
% 2.89/1.01      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_4777,c_3888,c_4610]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5347,plain,
% 2.89/1.01      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.89/1.01      | sK2 = k1_xboole_0
% 2.89/1.01      | sK5 = X0
% 2.89/1.01      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 2.89/1.01      inference(renaming,[status(thm)],[c_5346]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5359,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | sK5 = sK4
% 2.89/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.89/1.01      inference(equality_resolution,[status(thm)],[c_5347]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_28,negated_conjecture,
% 2.89/1.01      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.89/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_45,plain,
% 2.89/1.01      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4944,plain,
% 2.89/1.01      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.89/1.01      | ~ r2_hidden(sK4,k1_relat_1(sK3))
% 2.89/1.01      | ~ sP0_iProver_split
% 2.89/1.01      | k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK4)
% 2.89/1.01      | sK4 = sK5 ),
% 2.89/1.01      inference(instantiation,[status(thm)],[c_2332]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_4945,plain,
% 2.89/1.01      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK4)
% 2.89/1.01      | sK4 = sK5
% 2.89/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | sP0_iProver_split != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_4944]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5512,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.89/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_5359,c_45,c_3888,c_4605,c_4610,c_4611,c_4945]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5519,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0
% 2.89/1.01      | r2_hidden(sK5,sK2) != iProver_top
% 2.89/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4179,c_5512]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_30,negated_conjecture,
% 2.89/1.01      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.89/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_43,plain,
% 2.89/1.01      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5608,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_5519,c_43,c_4605]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5614,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 | r2_hidden(sK4,sK2) != iProver_top ),
% 2.89/1.01      inference(superposition,[status(thm)],[c_4179,c_5608]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_31,negated_conjecture,
% 2.89/1.01      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.89/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_42,plain,
% 2.89/1.01      ( r2_hidden(sK4,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5665,plain,
% 2.89/1.01      ( sK2 = k1_xboole_0 ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_5614,c_42,c_4605]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5673,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5665,c_4014]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_26,plain,
% 2.89/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.89/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.89/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.89/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_934,plain,
% 2.89/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.89/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.89/1.01      | sK2 != X1
% 2.89/1.01      | sK2 != k1_xboole_0
% 2.89/1.01      | sK3 != X0 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_935,plain,
% 2.89/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.89/1.01      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.89/1.01      | sK2 != k1_xboole_0 ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_934]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2973,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.89/1.01      | sK2 != k1_xboole_0
% 2.89/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_7,plain,
% 2.89/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_3099,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.89/1.01      | sK2 != k1_xboole_0
% 2.89/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_2973,c_7]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5675,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.89/1.01      | k1_xboole_0 != k1_xboole_0
% 2.89/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5665,c_3099]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5692,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.89/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.01      inference(equality_resolution_simp,[status(thm)],[c_5675]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5680,plain,
% 2.89/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5665,c_2986]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5682,plain,
% 2.89/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5680,c_7]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5695,plain,
% 2.89/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 2.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5692,c_5682]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5700,plain,
% 2.89/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.89/1.01      inference(light_normalisation,[status(thm)],[c_5673,c_5695]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5873,plain,
% 2.89/1.01      ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) = iProver_top
% 2.89/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5700,c_2979]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2989,plain,
% 2.89/1.01      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5678,plain,
% 2.89/1.01      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 2.89/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(demodulation,[status(thm)],[c_5665,c_2989]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_0,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.89/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_1,plain,
% 2.89/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.89/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_440,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.89/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_441,plain,
% 2.89/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.89/1.01      inference(unflattening,[status(thm)],[c_440]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_2984,plain,
% 2.89/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.89/1.01      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_5719,plain,
% 2.89/1.01      ( v2_funct_1(sK3) != iProver_top ),
% 2.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5678,c_2984]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_6014,plain,
% 2.89/1.01      ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top ),
% 2.89/1.01      inference(global_propositional_subsumption,
% 2.89/1.01                [status(thm)],
% 2.89/1.01                [c_5873,c_3888,c_5719]) ).
% 2.89/1.01  
% 2.89/1.01  cnf(c_6019,plain,
% 2.89/1.01      ( $false ),
% 2.89/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6014,c_2984]) ).
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/1.01  
% 2.89/1.01  ------                               Statistics
% 2.89/1.01  
% 2.89/1.01  ------ General
% 2.89/1.01  
% 2.89/1.01  abstr_ref_over_cycles:                  0
% 2.89/1.01  abstr_ref_under_cycles:                 0
% 2.89/1.01  gc_basic_clause_elim:                   0
% 2.89/1.01  forced_gc_time:                         0
% 2.89/1.01  parsing_time:                           0.011
% 2.89/1.01  unif_index_cands_time:                  0.
% 2.89/1.01  unif_index_add_time:                    0.
% 2.89/1.01  orderings_time:                         0.
% 2.89/1.01  out_proof_time:                         0.01
% 2.89/1.01  total_time:                             0.167
% 2.89/1.01  num_of_symbols:                         53
% 2.89/1.01  num_of_terms:                           3132
% 2.89/1.01  
% 2.89/1.01  ------ Preprocessing
% 2.89/1.01  
% 2.89/1.01  num_of_splits:                          1
% 2.89/1.01  num_of_split_atoms:                     1
% 2.89/1.01  num_of_reused_defs:                     0
% 2.89/1.01  num_eq_ax_congr_red:                    11
% 2.89/1.01  num_of_sem_filtered_clauses:            1
% 2.89/1.01  num_of_subtypes:                        0
% 2.89/1.01  monotx_restored_types:                  0
% 2.89/1.01  sat_num_of_epr_types:                   0
% 2.89/1.01  sat_num_of_non_cyclic_types:            0
% 2.89/1.01  sat_guarded_non_collapsed_types:        0
% 2.89/1.01  num_pure_diseq_elim:                    0
% 2.89/1.01  simp_replaced_by:                       0
% 2.89/1.01  res_preprocessed:                       155
% 2.89/1.01  prep_upred:                             0
% 2.89/1.01  prep_unflattend:                        60
% 2.89/1.01  smt_new_axioms:                         0
% 2.89/1.01  pred_elim_cands:                        5
% 2.89/1.01  pred_elim:                              3
% 2.89/1.01  pred_elim_cl:                           6
% 2.89/1.01  pred_elim_cycles:                       8
% 2.89/1.01  merged_defs:                            8
% 2.89/1.01  merged_defs_ncl:                        0
% 2.89/1.01  bin_hyper_res:                          9
% 2.89/1.01  prep_cycles:                            4
% 2.89/1.01  pred_elim_time:                         0.024
% 2.89/1.01  splitting_time:                         0.
% 2.89/1.01  sem_filter_time:                        0.
% 2.89/1.01  monotx_time:                            0.
% 2.89/1.01  subtype_inf_time:                       0.
% 2.89/1.01  
% 2.89/1.01  ------ Problem properties
% 2.89/1.01  
% 2.89/1.01  clauses:                                30
% 2.89/1.01  conjectures:                            6
% 2.89/1.01  epr:                                    9
% 2.89/1.01  horn:                                   23
% 2.89/1.01  ground:                                 13
% 2.89/1.01  unary:                                  7
% 2.89/1.01  binary:                                 8
% 2.89/1.01  lits:                                   73
% 2.89/1.01  lits_eq:                                23
% 2.89/1.01  fd_pure:                                0
% 2.89/1.01  fd_pseudo:                              0
% 2.89/1.01  fd_cond:                                1
% 2.89/1.01  fd_pseudo_cond:                         4
% 2.89/1.01  ac_symbols:                             0
% 2.89/1.01  
% 2.89/1.01  ------ Propositional Solver
% 2.89/1.01  
% 2.89/1.01  prop_solver_calls:                      29
% 2.89/1.01  prop_fast_solver_calls:                 1325
% 2.89/1.01  smt_solver_calls:                       0
% 2.89/1.01  smt_fast_solver_calls:                  0
% 2.89/1.01  prop_num_of_clauses:                    1384
% 2.89/1.01  prop_preprocess_simplified:             5730
% 2.89/1.01  prop_fo_subsumed:                       23
% 2.89/1.01  prop_solver_time:                       0.
% 2.89/1.01  smt_solver_time:                        0.
% 2.89/1.01  smt_fast_solver_time:                   0.
% 2.89/1.01  prop_fast_solver_time:                  0.
% 2.89/1.01  prop_unsat_core_time:                   0.
% 2.89/1.01  
% 2.89/1.01  ------ QBF
% 2.89/1.01  
% 2.89/1.01  qbf_q_res:                              0
% 2.89/1.01  qbf_num_tautologies:                    0
% 2.89/1.01  qbf_prep_cycles:                        0
% 2.89/1.01  
% 2.89/1.01  ------ BMC1
% 2.89/1.01  
% 2.89/1.01  bmc1_current_bound:                     -1
% 2.89/1.01  bmc1_last_solved_bound:                 -1
% 2.89/1.01  bmc1_unsat_core_size:                   -1
% 2.89/1.01  bmc1_unsat_core_parents_size:           -1
% 2.89/1.01  bmc1_merge_next_fun:                    0
% 2.89/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.89/1.01  
% 2.89/1.01  ------ Instantiation
% 2.89/1.01  
% 2.89/1.01  inst_num_of_clauses:                    385
% 2.89/1.01  inst_num_in_passive:                    154
% 2.89/1.01  inst_num_in_active:                     229
% 2.89/1.01  inst_num_in_unprocessed:                2
% 2.89/1.01  inst_num_of_loops:                      320
% 2.89/1.01  inst_num_of_learning_restarts:          0
% 2.89/1.01  inst_num_moves_active_passive:          87
% 2.89/1.01  inst_lit_activity:                      0
% 2.89/1.01  inst_lit_activity_moves:                0
% 2.89/1.01  inst_num_tautologies:                   0
% 2.89/1.01  inst_num_prop_implied:                  0
% 2.89/1.01  inst_num_existing_simplified:           0
% 2.89/1.01  inst_num_eq_res_simplified:             0
% 2.89/1.01  inst_num_child_elim:                    0
% 2.89/1.01  inst_num_of_dismatching_blockings:      130
% 2.89/1.01  inst_num_of_non_proper_insts:           527
% 2.89/1.01  inst_num_of_duplicates:                 0
% 2.89/1.01  inst_inst_num_from_inst_to_res:         0
% 2.89/1.01  inst_dismatching_checking_time:         0.
% 2.89/1.01  
% 2.89/1.01  ------ Resolution
% 2.89/1.01  
% 2.89/1.01  res_num_of_clauses:                     0
% 2.89/1.01  res_num_in_passive:                     0
% 2.89/1.01  res_num_in_active:                      0
% 2.89/1.01  res_num_of_loops:                       159
% 2.89/1.01  res_forward_subset_subsumed:            25
% 2.89/1.01  res_backward_subset_subsumed:           0
% 2.89/1.01  res_forward_subsumed:                   1
% 2.89/1.01  res_backward_subsumed:                  0
% 2.89/1.01  res_forward_subsumption_resolution:     1
% 2.89/1.01  res_backward_subsumption_resolution:    0
% 2.89/1.01  res_clause_to_clause_subsumption:       174
% 2.89/1.01  res_orphan_elimination:                 0
% 2.89/1.01  res_tautology_del:                      87
% 2.89/1.01  res_num_eq_res_simplified:              0
% 2.89/1.01  res_num_sel_changes:                    0
% 2.89/1.01  res_moves_from_active_to_pass:          0
% 2.89/1.01  
% 2.89/1.01  ------ Superposition
% 2.89/1.01  
% 2.89/1.01  sup_time_total:                         0.
% 2.89/1.01  sup_time_generating:                    0.
% 2.89/1.01  sup_time_sim_full:                      0.
% 2.89/1.01  sup_time_sim_immed:                     0.
% 2.89/1.01  
% 2.89/1.01  sup_num_of_clauses:                     45
% 2.89/1.01  sup_num_in_active:                      32
% 2.89/1.01  sup_num_in_passive:                     13
% 2.89/1.01  sup_num_of_loops:                       63
% 2.89/1.01  sup_fw_superposition:                   40
% 2.89/1.01  sup_bw_superposition:                   28
% 2.89/1.01  sup_immediate_simplified:               21
% 2.89/1.01  sup_given_eliminated:                   0
% 2.89/1.01  comparisons_done:                       0
% 2.89/1.01  comparisons_avoided:                    6
% 2.89/1.01  
% 2.89/1.01  ------ Simplifications
% 2.89/1.01  
% 2.89/1.01  
% 2.89/1.01  sim_fw_subset_subsumed:                 9
% 2.89/1.01  sim_bw_subset_subsumed:                 13
% 2.89/1.01  sim_fw_subsumed:                        7
% 2.89/1.01  sim_bw_subsumed:                        0
% 2.89/1.01  sim_fw_subsumption_res:                 4
% 2.89/1.01  sim_bw_subsumption_res:                 0
% 2.89/1.01  sim_tautology_del:                      5
% 2.89/1.01  sim_eq_tautology_del:                   12
% 2.89/1.01  sim_eq_res_simp:                        1
% 2.89/1.01  sim_fw_demodulated:                     5
% 2.89/1.01  sim_bw_demodulated:                     20
% 2.89/1.01  sim_light_normalised:                   3
% 2.89/1.01  sim_joinable_taut:                      0
% 2.89/1.01  sim_joinable_simp:                      0
% 2.89/1.01  sim_ac_normalised:                      0
% 2.89/1.01  sim_smt_subsumption:                    0
% 2.89/1.01  
%------------------------------------------------------------------------------
