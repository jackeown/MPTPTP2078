%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:56 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  167 (43154 expanded)
%              Number of clauses        :  122 (14131 expanded)
%              Number of leaves         :   12 (8302 expanded)
%              Depth                    :   45
%              Number of atoms          :  668 (319549 expanded)
%              Number of equality atoms :  373 (112187 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK7 != sK8
        & k1_funct_1(X1,sK7) = k1_funct_1(X1,sK8)
        & r2_hidden(sK8,X0)
        & r2_hidden(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
            & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3)
            & r2_hidden(X3,sK5)
            & r2_hidden(X2,sK5) )
        | ~ v2_funct_1(sK6) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
            | ~ r2_hidden(X5,sK5)
            | ~ r2_hidden(X4,sK5) )
        | v2_funct_1(sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
      & v1_funct_2(sK6,sK5,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( sK7 != sK8
        & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
        & r2_hidden(sK8,sK5)
        & r2_hidden(sK7,sK5) )
      | ~ v2_funct_1(sK6) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
          | ~ r2_hidden(X5,sK5)
          | ~ r2_hidden(X4,sK5) )
      | v2_funct_1(sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    & v1_funct_2(sK6,sK5,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f39,f41,f40])).

fof(f72,plain,(
    v1_funct_2(sK6,sK5,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X4,sK5)
      | v2_funct_1(sK6) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,
    ( sK7 != sK8
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,
    ( r2_hidden(sK7,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,
    ( r2_hidden(sK8,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK5,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_425,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_576,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK5 != X0
    | sK5 != X1
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_425])).

cnf(c_577,plain,
    ( k1_relset_1(sK5,sK5,sK6) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_2930,plain,
    ( k1_relset_1(sK5,sK5,sK6) = sK5
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_577])).

cnf(c_5193,plain,
    ( k1_relset_1(sK5,sK5,sK6) = sK5
    | k1_xboole_0 = sK5 ),
    inference(subtyping,[status(esa)],[c_2930])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_460,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_461,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_5196,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | k1_relset_1(X0_51,X1_51,sK6) = k1_relat_1(sK6) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_6144,plain,
    ( k1_relset_1(sK5,sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_5196])).

cnf(c_6268,plain,
    ( k1_relat_1(sK6) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5193,c_6144])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5220,plain,
    ( r2_hidden(sK2(X0_51),k1_relat_1(X0_51))
    | ~ v1_funct_1(X0_51)
    | v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5764,plain,
    ( r2_hidden(sK2(X0_51),k1_relat_1(X0_51)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5220])).

cnf(c_6507,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(sK6),sK5) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_5764])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5226,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_6098,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_5226])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_409,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_33])).

cnf(c_410,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_5197,plain,
    ( ~ v1_relat_1(X0_51)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_6093,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_5197])).

cnf(c_6214,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK5))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_6093])).

cnf(c_6215,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | v1_relat_1(k2_zfmisc_1(sK5,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6214])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5223,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6246,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_5223])).

cnf(c_6247,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6246])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5219,plain,
    ( r2_hidden(sK1(X0_51),k1_relat_1(X0_51))
    | ~ v1_funct_1(X0_51)
    | v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5765,plain,
    ( r2_hidden(sK1(X0_51),k1_relat_1(X0_51)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5219])).

cnf(c_6569,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6),sK5) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_5765])).

cnf(c_5199,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_5785,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5199])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5221,plain,
    ( ~ v1_funct_1(X0_51)
    | v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_funct_1(X0_51,sK2(X0_51)) = k1_funct_1(X0_51,sK1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5763,plain,
    ( k1_funct_1(X0_51,sK2(X0_51)) = k1_funct_1(X0_51,sK1(X0_51))
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5221])).

cnf(c_6480,plain,
    ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5785,c_5763])).

cnf(c_6145,plain,
    ( ~ v1_funct_1(sK6)
    | v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6)) ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_6146,plain,
    ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6145])).

cnf(c_6633,plain,
    ( v2_funct_1(sK6) = iProver_top
    | k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_36,c_6098,c_6146,c_6215,c_6247])).

cnf(c_6634,plain,
    ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
    | v2_funct_1(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_6633])).

cnf(c_29,negated_conjecture,
    ( ~ v2_funct_1(sK6)
    | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5203,negated_conjecture,
    ( ~ v2_funct_1(sK6)
    | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_5781,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5203])).

cnf(c_6639,plain,
    ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
    | k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_6634,c_5781])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK5)
    | v2_funct_1(sK6)
    | X1 = X0
    | k1_funct_1(sK6,X1) != k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5200,negated_conjecture,
    ( ~ r2_hidden(X0_53,sK5)
    | ~ r2_hidden(X1_53,sK5)
    | v2_funct_1(sK6)
    | X1_53 = X0_53
    | k1_funct_1(sK6,X1_53) != k1_funct_1(sK6,X0_53) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_5784,plain,
    ( X0_53 = X1_53
    | k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,X1_53)
    | r2_hidden(X0_53,sK5) != iProver_top
    | r2_hidden(X1_53,sK5) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5200])).

cnf(c_6682,plain,
    ( k1_funct_1(sK6,sK1(sK6)) != k1_funct_1(sK6,X0_53)
    | k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
    | sK2(sK6) = X0_53
    | r2_hidden(X0_53,sK5) != iProver_top
    | r2_hidden(sK2(sK6),sK5) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6639,c_5784])).

cnf(c_6741,plain,
    ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
    | sK2(sK6) = sK1(sK6)
    | r2_hidden(sK2(sK6),sK5) != iProver_top
    | r2_hidden(sK1(sK6),sK5) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6682])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5222,plain,
    ( ~ v1_funct_1(X0_51)
    | v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | sK2(X0_51) != sK1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6136,plain,
    ( ~ v1_funct_1(sK6)
    | v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sK2(sK6) != sK1(sK6) ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_6137,plain,
    ( sK2(sK6) != sK1(sK6)
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6136])).

cnf(c_6442,plain,
    ( ~ r2_hidden(sK2(sK6),sK5)
    | ~ r2_hidden(sK1(sK6),sK5)
    | v2_funct_1(sK6)
    | k1_funct_1(sK6,sK2(sK6)) != k1_funct_1(sK6,sK1(sK6))
    | sK2(sK6) = sK1(sK6) ),
    inference(instantiation,[status(thm)],[c_5200])).

cnf(c_6443,plain,
    ( k1_funct_1(sK6,sK2(sK6)) != k1_funct_1(sK6,sK1(sK6))
    | sK2(sK6) = sK1(sK6)
    | r2_hidden(sK2(sK6),sK5) != iProver_top
    | r2_hidden(sK1(sK6),sK5) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6442])).

cnf(c_6863,plain,
    ( r2_hidden(sK2(sK6),sK5) != iProver_top
    | r2_hidden(sK1(sK6),sK5) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6741,c_36,c_6098,c_6137,c_6146,c_6215,c_6247,c_6443])).

cnf(c_6995,plain,
    ( v2_funct_1(sK6) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6507,c_36,c_6098,c_6215,c_6247,c_6569,c_6863])).

cnf(c_6996,plain,
    ( sK5 = k1_xboole_0
    | v2_funct_1(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_6995])).

cnf(c_7001,plain,
    ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6996,c_5781])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5218,plain,
    ( ~ r2_hidden(X0_53,k1_relat_1(X0_51))
    | ~ r2_hidden(X1_53,k1_relat_1(X0_51))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | X0_53 = X1_53
    | k1_funct_1(X0_51,X0_53) != k1_funct_1(X0_51,X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5766,plain,
    ( X0_53 = X1_53
    | k1_funct_1(X0_51,X0_53) != k1_funct_1(X0_51,X1_53)
    | r2_hidden(X1_53,k1_relat_1(X0_51)) != iProver_top
    | r2_hidden(X0_53,k1_relat_1(X0_51)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5218])).

cnf(c_7126,plain,
    ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
    | sK8 = X0_53
    | sK5 = k1_xboole_0
    | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7001,c_5766])).

cnf(c_7363,plain,
    ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
    | sK5 = k1_xboole_0
    | sK8 = X0_53
    | k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7126,c_36,c_6098,c_6215,c_6247,c_6996])).

cnf(c_7364,plain,
    ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
    | sK8 = X0_53
    | sK5 = k1_xboole_0
    | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7363])).

cnf(c_7376,plain,
    ( sK8 = sK7
    | sK5 = k1_xboole_0
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7364])).

cnf(c_28,negated_conjecture,
    ( ~ v2_funct_1(sK6)
    | sK7 != sK8 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5204,negated_conjecture,
    ( ~ v2_funct_1(sK6)
    | sK7 != sK8 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5300,plain,
    ( sK7 != sK8
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5204])).

cnf(c_5301,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5203])).

cnf(c_6619,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(X0_51))
    | ~ r2_hidden(sK7,k1_relat_1(X0_51))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_funct_1(X0_51,sK7) != k1_funct_1(X0_51,sK8)
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_5218])).

cnf(c_6977,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(sK6))
    | ~ r2_hidden(sK7,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK7) != k1_funct_1(sK6,sK8)
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_6619])).

cnf(c_6978,plain,
    ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,sK8)
    | sK7 = sK8
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6977])).

cnf(c_7453,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7376,c_36,c_5300,c_5301,c_6098,c_6215,c_6247,c_6978,c_6996])).

cnf(c_7460,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_7453])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK7,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( r2_hidden(sK7,sK5) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7495,plain,
    ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7460,c_42,c_6996])).

cnf(c_7496,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7495])).

cnf(c_7501,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_7496])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK8,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( r2_hidden(sK8,sK5) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7504,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7501,c_43,c_6996])).

cnf(c_7509,plain,
    ( r2_hidden(sK2(sK6),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK6),k1_xboole_0) != iProver_top
    | v2_funct_1(sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7504,c_6863])).

cnf(c_7512,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_7504,c_6144])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_504,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_505,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_601,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK5 != X0
    | sK5 != k1_xboole_0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_505])).

cnf(c_602,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | sK5 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_5194,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_602])).

cnf(c_7516,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7504,c_5194])).

cnf(c_7532,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7516])).

cnf(c_7545,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7512,c_7532])).

cnf(c_8020,plain,
    ( r2_hidden(sK1(sK6),k1_xboole_0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7545,c_5765])).

cnf(c_8021,plain,
    ( r2_hidden(sK2(sK6),k1_xboole_0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7545,c_5764])).

cnf(c_8117,plain,
    ( v2_funct_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7509,c_36,c_6098,c_6215,c_6247,c_8020,c_8021])).

cnf(c_8123,plain,
    ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_8117,c_5781])).

cnf(c_8240,plain,
    ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
    | sK8 = X0_53
    | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8123,c_5766])).

cnf(c_8248,plain,
    ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
    | sK8 = X0_53
    | r2_hidden(X0_53,k1_xboole_0) != iProver_top
    | r2_hidden(sK8,k1_xboole_0) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8240,c_7545])).

cnf(c_5202,negated_conjecture,
    ( r2_hidden(sK8,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_5782,plain,
    ( r2_hidden(sK8,sK5) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5202])).

cnf(c_7519,plain,
    ( r2_hidden(sK8,k1_xboole_0) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7504,c_5782])).

cnf(c_8507,plain,
    ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
    | sK8 = X0_53
    | r2_hidden(X0_53,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8248,c_36,c_6098,c_6215,c_6247,c_7509,c_7519,c_8020,c_8021])).

cnf(c_8519,plain,
    ( sK8 = sK7
    | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8507])).

cnf(c_5201,negated_conjecture,
    ( r2_hidden(sK7,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_5783,plain,
    ( r2_hidden(sK7,sK5) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5201])).

cnf(c_7518,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | v2_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7504,c_5783])).

cnf(c_5230,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_6624,plain,
    ( sK8 != X0_53
    | sK7 != X0_53
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_5230])).

cnf(c_6625,plain,
    ( sK8 != sK7
    | sK7 = sK8
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_6624])).

cnf(c_5227,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_5254,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_5227])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8519,c_8117,c_7518,c_6625,c_5300,c_5254])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:46:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.04/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/1.00  
% 3.04/1.00  ------  iProver source info
% 3.04/1.00  
% 3.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/1.00  git: non_committed_changes: false
% 3.04/1.00  git: last_make_outside_of_git: false
% 3.04/1.00  
% 3.04/1.00  ------ 
% 3.04/1.00  
% 3.04/1.00  ------ Input Options
% 3.04/1.00  
% 3.04/1.00  --out_options                           all
% 3.04/1.00  --tptp_safe_out                         true
% 3.04/1.00  --problem_path                          ""
% 3.04/1.00  --include_path                          ""
% 3.04/1.00  --clausifier                            res/vclausify_rel
% 3.04/1.00  --clausifier_options                    --mode clausify
% 3.04/1.00  --stdin                                 false
% 3.04/1.00  --stats_out                             all
% 3.04/1.00  
% 3.04/1.00  ------ General Options
% 3.04/1.00  
% 3.04/1.00  --fof                                   false
% 3.04/1.00  --time_out_real                         305.
% 3.04/1.00  --time_out_virtual                      -1.
% 3.04/1.00  --symbol_type_check                     false
% 3.04/1.00  --clausify_out                          false
% 3.04/1.00  --sig_cnt_out                           false
% 3.04/1.00  --trig_cnt_out                          false
% 3.04/1.00  --trig_cnt_out_tolerance                1.
% 3.04/1.00  --trig_cnt_out_sk_spl                   false
% 3.04/1.00  --abstr_cl_out                          false
% 3.04/1.00  
% 3.04/1.00  ------ Global Options
% 3.04/1.00  
% 3.04/1.00  --schedule                              default
% 3.04/1.00  --add_important_lit                     false
% 3.04/1.00  --prop_solver_per_cl                    1000
% 3.04/1.00  --min_unsat_core                        false
% 3.04/1.00  --soft_assumptions                      false
% 3.04/1.00  --soft_lemma_size                       3
% 3.04/1.00  --prop_impl_unit_size                   0
% 3.04/1.00  --prop_impl_unit                        []
% 3.04/1.00  --share_sel_clauses                     true
% 3.04/1.00  --reset_solvers                         false
% 3.04/1.00  --bc_imp_inh                            [conj_cone]
% 3.04/1.00  --conj_cone_tolerance                   3.
% 3.04/1.00  --extra_neg_conj                        none
% 3.04/1.00  --large_theory_mode                     true
% 3.04/1.00  --prolific_symb_bound                   200
% 3.04/1.00  --lt_threshold                          2000
% 3.04/1.00  --clause_weak_htbl                      true
% 3.04/1.00  --gc_record_bc_elim                     false
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing Options
% 3.04/1.00  
% 3.04/1.00  --preprocessing_flag                    true
% 3.04/1.00  --time_out_prep_mult                    0.1
% 3.04/1.00  --splitting_mode                        input
% 3.04/1.00  --splitting_grd                         true
% 3.04/1.00  --splitting_cvd                         false
% 3.04/1.00  --splitting_cvd_svl                     false
% 3.04/1.00  --splitting_nvd                         32
% 3.04/1.00  --sub_typing                            true
% 3.04/1.00  --prep_gs_sim                           true
% 3.04/1.00  --prep_unflatten                        true
% 3.04/1.00  --prep_res_sim                          true
% 3.04/1.00  --prep_upred                            true
% 3.04/1.00  --prep_sem_filter                       exhaustive
% 3.04/1.00  --prep_sem_filter_out                   false
% 3.04/1.00  --pred_elim                             true
% 3.04/1.00  --res_sim_input                         true
% 3.04/1.00  --eq_ax_congr_red                       true
% 3.04/1.00  --pure_diseq_elim                       true
% 3.04/1.00  --brand_transform                       false
% 3.04/1.00  --non_eq_to_eq                          false
% 3.04/1.00  --prep_def_merge                        true
% 3.04/1.00  --prep_def_merge_prop_impl              false
% 3.04/1.00  --prep_def_merge_mbd                    true
% 3.04/1.00  --prep_def_merge_tr_red                 false
% 3.04/1.00  --prep_def_merge_tr_cl                  false
% 3.04/1.00  --smt_preprocessing                     true
% 3.04/1.00  --smt_ac_axioms                         fast
% 3.04/1.00  --preprocessed_out                      false
% 3.04/1.00  --preprocessed_stats                    false
% 3.04/1.00  
% 3.04/1.00  ------ Abstraction refinement Options
% 3.04/1.00  
% 3.04/1.00  --abstr_ref                             []
% 3.04/1.00  --abstr_ref_prep                        false
% 3.04/1.00  --abstr_ref_until_sat                   false
% 3.04/1.00  --abstr_ref_sig_restrict                funpre
% 3.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/1.00  --abstr_ref_under                       []
% 3.04/1.00  
% 3.04/1.00  ------ SAT Options
% 3.04/1.00  
% 3.04/1.00  --sat_mode                              false
% 3.04/1.00  --sat_fm_restart_options                ""
% 3.04/1.00  --sat_gr_def                            false
% 3.04/1.00  --sat_epr_types                         true
% 3.04/1.00  --sat_non_cyclic_types                  false
% 3.04/1.00  --sat_finite_models                     false
% 3.04/1.00  --sat_fm_lemmas                         false
% 3.04/1.00  --sat_fm_prep                           false
% 3.04/1.00  --sat_fm_uc_incr                        true
% 3.04/1.00  --sat_out_model                         small
% 3.04/1.00  --sat_out_clauses                       false
% 3.04/1.00  
% 3.04/1.00  ------ QBF Options
% 3.04/1.00  
% 3.04/1.00  --qbf_mode                              false
% 3.04/1.00  --qbf_elim_univ                         false
% 3.04/1.00  --qbf_dom_inst                          none
% 3.04/1.00  --qbf_dom_pre_inst                      false
% 3.04/1.00  --qbf_sk_in                             false
% 3.04/1.00  --qbf_pred_elim                         true
% 3.04/1.00  --qbf_split                             512
% 3.04/1.00  
% 3.04/1.00  ------ BMC1 Options
% 3.04/1.00  
% 3.04/1.00  --bmc1_incremental                      false
% 3.04/1.00  --bmc1_axioms                           reachable_all
% 3.04/1.00  --bmc1_min_bound                        0
% 3.04/1.00  --bmc1_max_bound                        -1
% 3.04/1.00  --bmc1_max_bound_default                -1
% 3.04/1.00  --bmc1_symbol_reachability              true
% 3.04/1.00  --bmc1_property_lemmas                  false
% 3.04/1.00  --bmc1_k_induction                      false
% 3.04/1.00  --bmc1_non_equiv_states                 false
% 3.04/1.00  --bmc1_deadlock                         false
% 3.04/1.00  --bmc1_ucm                              false
% 3.04/1.00  --bmc1_add_unsat_core                   none
% 3.04/1.00  --bmc1_unsat_core_children              false
% 3.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/1.00  --bmc1_out_stat                         full
% 3.04/1.00  --bmc1_ground_init                      false
% 3.04/1.00  --bmc1_pre_inst_next_state              false
% 3.04/1.00  --bmc1_pre_inst_state                   false
% 3.04/1.00  --bmc1_pre_inst_reach_state             false
% 3.04/1.00  --bmc1_out_unsat_core                   false
% 3.04/1.00  --bmc1_aig_witness_out                  false
% 3.04/1.00  --bmc1_verbose                          false
% 3.04/1.00  --bmc1_dump_clauses_tptp                false
% 3.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.04/1.00  --bmc1_dump_file                        -
% 3.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.04/1.00  --bmc1_ucm_extend_mode                  1
% 3.04/1.00  --bmc1_ucm_init_mode                    2
% 3.04/1.00  --bmc1_ucm_cone_mode                    none
% 3.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.04/1.00  --bmc1_ucm_relax_model                  4
% 3.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/1.00  --bmc1_ucm_layered_model                none
% 3.04/1.00  --bmc1_ucm_max_lemma_size               10
% 3.04/1.00  
% 3.04/1.00  ------ AIG Options
% 3.04/1.00  
% 3.04/1.00  --aig_mode                              false
% 3.04/1.00  
% 3.04/1.00  ------ Instantiation Options
% 3.04/1.00  
% 3.04/1.00  --instantiation_flag                    true
% 3.04/1.00  --inst_sos_flag                         false
% 3.04/1.00  --inst_sos_phase                        true
% 3.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/1.00  --inst_lit_sel_side                     num_symb
% 3.04/1.00  --inst_solver_per_active                1400
% 3.04/1.00  --inst_solver_calls_frac                1.
% 3.04/1.00  --inst_passive_queue_type               priority_queues
% 3.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/1.00  --inst_passive_queues_freq              [25;2]
% 3.04/1.00  --inst_dismatching                      true
% 3.04/1.00  --inst_eager_unprocessed_to_passive     true
% 3.04/1.00  --inst_prop_sim_given                   true
% 3.04/1.00  --inst_prop_sim_new                     false
% 3.04/1.00  --inst_subs_new                         false
% 3.04/1.00  --inst_eq_res_simp                      false
% 3.04/1.00  --inst_subs_given                       false
% 3.04/1.00  --inst_orphan_elimination               true
% 3.04/1.00  --inst_learning_loop_flag               true
% 3.04/1.00  --inst_learning_start                   3000
% 3.04/1.00  --inst_learning_factor                  2
% 3.04/1.00  --inst_start_prop_sim_after_learn       3
% 3.04/1.00  --inst_sel_renew                        solver
% 3.04/1.00  --inst_lit_activity_flag                true
% 3.04/1.00  --inst_restr_to_given                   false
% 3.04/1.00  --inst_activity_threshold               500
% 3.04/1.00  --inst_out_proof                        true
% 3.04/1.00  
% 3.04/1.00  ------ Resolution Options
% 3.04/1.00  
% 3.04/1.00  --resolution_flag                       true
% 3.04/1.00  --res_lit_sel                           adaptive
% 3.04/1.00  --res_lit_sel_side                      none
% 3.04/1.00  --res_ordering                          kbo
% 3.04/1.00  --res_to_prop_solver                    active
% 3.04/1.00  --res_prop_simpl_new                    false
% 3.04/1.00  --res_prop_simpl_given                  true
% 3.04/1.00  --res_passive_queue_type                priority_queues
% 3.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/1.00  --res_passive_queues_freq               [15;5]
% 3.04/1.00  --res_forward_subs                      full
% 3.04/1.00  --res_backward_subs                     full
% 3.04/1.00  --res_forward_subs_resolution           true
% 3.04/1.00  --res_backward_subs_resolution          true
% 3.04/1.00  --res_orphan_elimination                true
% 3.04/1.00  --res_time_limit                        2.
% 3.04/1.00  --res_out_proof                         true
% 3.04/1.00  
% 3.04/1.00  ------ Superposition Options
% 3.04/1.00  
% 3.04/1.00  --superposition_flag                    true
% 3.04/1.00  --sup_passive_queue_type                priority_queues
% 3.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.04/1.00  --demod_completeness_check              fast
% 3.04/1.00  --demod_use_ground                      true
% 3.04/1.00  --sup_to_prop_solver                    passive
% 3.04/1.00  --sup_prop_simpl_new                    true
% 3.04/1.00  --sup_prop_simpl_given                  true
% 3.04/1.00  --sup_fun_splitting                     false
% 3.04/1.00  --sup_smt_interval                      50000
% 3.04/1.00  
% 3.04/1.00  ------ Superposition Simplification Setup
% 3.04/1.00  
% 3.04/1.00  --sup_indices_passive                   []
% 3.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_full_bw                           [BwDemod]
% 3.04/1.00  --sup_immed_triv                        [TrivRules]
% 3.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_immed_bw_main                     []
% 3.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/1.00  
% 3.04/1.00  ------ Combination Options
% 3.04/1.00  
% 3.04/1.00  --comb_res_mult                         3
% 3.04/1.00  --comb_sup_mult                         2
% 3.04/1.00  --comb_inst_mult                        10
% 3.04/1.00  
% 3.04/1.00  ------ Debug Options
% 3.04/1.00  
% 3.04/1.00  --dbg_backtrace                         false
% 3.04/1.00  --dbg_dump_prop_clauses                 false
% 3.04/1.00  --dbg_dump_prop_clauses_file            -
% 3.04/1.00  --dbg_out_stat                          false
% 3.04/1.00  ------ Parsing...
% 3.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/1.00  ------ Proving...
% 3.04/1.00  ------ Problem Properties 
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  clauses                                 31
% 3.04/1.00  conjectures                             6
% 3.04/1.00  EPR                                     4
% 3.04/1.00  Horn                                    21
% 3.04/1.00  unary                                   2
% 3.04/1.00  binary                                  9
% 3.04/1.00  lits                                    122
% 3.04/1.00  lits eq                                 32
% 3.04/1.00  fd_pure                                 0
% 3.04/1.00  fd_pseudo                               0
% 3.04/1.00  fd_cond                                 0
% 3.04/1.00  fd_pseudo_cond                          6
% 3.04/1.00  AC symbols                              0
% 3.04/1.00  
% 3.04/1.00  ------ Schedule dynamic 5 is on 
% 3.04/1.00  
% 3.04/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  ------ 
% 3.04/1.00  Current options:
% 3.04/1.00  ------ 
% 3.04/1.00  
% 3.04/1.00  ------ Input Options
% 3.04/1.00  
% 3.04/1.00  --out_options                           all
% 3.04/1.00  --tptp_safe_out                         true
% 3.04/1.00  --problem_path                          ""
% 3.04/1.00  --include_path                          ""
% 3.04/1.00  --clausifier                            res/vclausify_rel
% 3.04/1.00  --clausifier_options                    --mode clausify
% 3.04/1.00  --stdin                                 false
% 3.04/1.00  --stats_out                             all
% 3.04/1.00  
% 3.04/1.00  ------ General Options
% 3.04/1.00  
% 3.04/1.00  --fof                                   false
% 3.04/1.00  --time_out_real                         305.
% 3.04/1.00  --time_out_virtual                      -1.
% 3.04/1.00  --symbol_type_check                     false
% 3.04/1.00  --clausify_out                          false
% 3.04/1.00  --sig_cnt_out                           false
% 3.04/1.00  --trig_cnt_out                          false
% 3.04/1.00  --trig_cnt_out_tolerance                1.
% 3.04/1.00  --trig_cnt_out_sk_spl                   false
% 3.04/1.00  --abstr_cl_out                          false
% 3.04/1.00  
% 3.04/1.00  ------ Global Options
% 3.04/1.00  
% 3.04/1.00  --schedule                              default
% 3.04/1.00  --add_important_lit                     false
% 3.04/1.00  --prop_solver_per_cl                    1000
% 3.04/1.00  --min_unsat_core                        false
% 3.04/1.00  --soft_assumptions                      false
% 3.04/1.00  --soft_lemma_size                       3
% 3.04/1.00  --prop_impl_unit_size                   0
% 3.04/1.00  --prop_impl_unit                        []
% 3.04/1.00  --share_sel_clauses                     true
% 3.04/1.00  --reset_solvers                         false
% 3.04/1.00  --bc_imp_inh                            [conj_cone]
% 3.04/1.00  --conj_cone_tolerance                   3.
% 3.04/1.00  --extra_neg_conj                        none
% 3.04/1.00  --large_theory_mode                     true
% 3.04/1.00  --prolific_symb_bound                   200
% 3.04/1.00  --lt_threshold                          2000
% 3.04/1.00  --clause_weak_htbl                      true
% 3.04/1.00  --gc_record_bc_elim                     false
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing Options
% 3.04/1.00  
% 3.04/1.00  --preprocessing_flag                    true
% 3.04/1.00  --time_out_prep_mult                    0.1
% 3.04/1.00  --splitting_mode                        input
% 3.04/1.00  --splitting_grd                         true
% 3.04/1.00  --splitting_cvd                         false
% 3.04/1.00  --splitting_cvd_svl                     false
% 3.04/1.00  --splitting_nvd                         32
% 3.04/1.00  --sub_typing                            true
% 3.04/1.00  --prep_gs_sim                           true
% 3.04/1.00  --prep_unflatten                        true
% 3.04/1.00  --prep_res_sim                          true
% 3.04/1.00  --prep_upred                            true
% 3.04/1.00  --prep_sem_filter                       exhaustive
% 3.04/1.00  --prep_sem_filter_out                   false
% 3.04/1.00  --pred_elim                             true
% 3.04/1.00  --res_sim_input                         true
% 3.04/1.00  --eq_ax_congr_red                       true
% 3.04/1.00  --pure_diseq_elim                       true
% 3.04/1.00  --brand_transform                       false
% 3.04/1.00  --non_eq_to_eq                          false
% 3.04/1.00  --prep_def_merge                        true
% 3.04/1.00  --prep_def_merge_prop_impl              false
% 3.04/1.00  --prep_def_merge_mbd                    true
% 3.04/1.00  --prep_def_merge_tr_red                 false
% 3.04/1.00  --prep_def_merge_tr_cl                  false
% 3.04/1.00  --smt_preprocessing                     true
% 3.04/1.00  --smt_ac_axioms                         fast
% 3.04/1.00  --preprocessed_out                      false
% 3.04/1.00  --preprocessed_stats                    false
% 3.04/1.00  
% 3.04/1.00  ------ Abstraction refinement Options
% 3.04/1.00  
% 3.04/1.00  --abstr_ref                             []
% 3.04/1.00  --abstr_ref_prep                        false
% 3.04/1.00  --abstr_ref_until_sat                   false
% 3.04/1.00  --abstr_ref_sig_restrict                funpre
% 3.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/1.00  --abstr_ref_under                       []
% 3.04/1.00  
% 3.04/1.00  ------ SAT Options
% 3.04/1.00  
% 3.04/1.00  --sat_mode                              false
% 3.04/1.00  --sat_fm_restart_options                ""
% 3.04/1.00  --sat_gr_def                            false
% 3.04/1.00  --sat_epr_types                         true
% 3.04/1.00  --sat_non_cyclic_types                  false
% 3.04/1.00  --sat_finite_models                     false
% 3.04/1.00  --sat_fm_lemmas                         false
% 3.04/1.00  --sat_fm_prep                           false
% 3.04/1.00  --sat_fm_uc_incr                        true
% 3.04/1.00  --sat_out_model                         small
% 3.04/1.00  --sat_out_clauses                       false
% 3.04/1.00  
% 3.04/1.00  ------ QBF Options
% 3.04/1.00  
% 3.04/1.00  --qbf_mode                              false
% 3.04/1.00  --qbf_elim_univ                         false
% 3.04/1.00  --qbf_dom_inst                          none
% 3.04/1.00  --qbf_dom_pre_inst                      false
% 3.04/1.00  --qbf_sk_in                             false
% 3.04/1.00  --qbf_pred_elim                         true
% 3.04/1.00  --qbf_split                             512
% 3.04/1.00  
% 3.04/1.00  ------ BMC1 Options
% 3.04/1.00  
% 3.04/1.00  --bmc1_incremental                      false
% 3.04/1.00  --bmc1_axioms                           reachable_all
% 3.04/1.00  --bmc1_min_bound                        0
% 3.04/1.00  --bmc1_max_bound                        -1
% 3.04/1.00  --bmc1_max_bound_default                -1
% 3.04/1.00  --bmc1_symbol_reachability              true
% 3.04/1.00  --bmc1_property_lemmas                  false
% 3.04/1.00  --bmc1_k_induction                      false
% 3.04/1.00  --bmc1_non_equiv_states                 false
% 3.04/1.00  --bmc1_deadlock                         false
% 3.04/1.00  --bmc1_ucm                              false
% 3.04/1.00  --bmc1_add_unsat_core                   none
% 3.04/1.00  --bmc1_unsat_core_children              false
% 3.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/1.00  --bmc1_out_stat                         full
% 3.04/1.00  --bmc1_ground_init                      false
% 3.04/1.00  --bmc1_pre_inst_next_state              false
% 3.04/1.00  --bmc1_pre_inst_state                   false
% 3.04/1.00  --bmc1_pre_inst_reach_state             false
% 3.04/1.00  --bmc1_out_unsat_core                   false
% 3.04/1.00  --bmc1_aig_witness_out                  false
% 3.04/1.00  --bmc1_verbose                          false
% 3.04/1.00  --bmc1_dump_clauses_tptp                false
% 3.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.04/1.00  --bmc1_dump_file                        -
% 3.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.04/1.00  --bmc1_ucm_extend_mode                  1
% 3.04/1.00  --bmc1_ucm_init_mode                    2
% 3.04/1.00  --bmc1_ucm_cone_mode                    none
% 3.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.04/1.00  --bmc1_ucm_relax_model                  4
% 3.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/1.00  --bmc1_ucm_layered_model                none
% 3.04/1.00  --bmc1_ucm_max_lemma_size               10
% 3.04/1.00  
% 3.04/1.00  ------ AIG Options
% 3.04/1.00  
% 3.04/1.00  --aig_mode                              false
% 3.04/1.00  
% 3.04/1.00  ------ Instantiation Options
% 3.04/1.00  
% 3.04/1.00  --instantiation_flag                    true
% 3.04/1.00  --inst_sos_flag                         false
% 3.04/1.00  --inst_sos_phase                        true
% 3.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/1.00  --inst_lit_sel_side                     none
% 3.04/1.00  --inst_solver_per_active                1400
% 3.04/1.00  --inst_solver_calls_frac                1.
% 3.04/1.00  --inst_passive_queue_type               priority_queues
% 3.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/1.00  --inst_passive_queues_freq              [25;2]
% 3.04/1.00  --inst_dismatching                      true
% 3.04/1.00  --inst_eager_unprocessed_to_passive     true
% 3.04/1.00  --inst_prop_sim_given                   true
% 3.04/1.00  --inst_prop_sim_new                     false
% 3.04/1.00  --inst_subs_new                         false
% 3.04/1.00  --inst_eq_res_simp                      false
% 3.04/1.00  --inst_subs_given                       false
% 3.04/1.00  --inst_orphan_elimination               true
% 3.04/1.00  --inst_learning_loop_flag               true
% 3.04/1.00  --inst_learning_start                   3000
% 3.04/1.00  --inst_learning_factor                  2
% 3.04/1.00  --inst_start_prop_sim_after_learn       3
% 3.04/1.00  --inst_sel_renew                        solver
% 3.04/1.00  --inst_lit_activity_flag                true
% 3.04/1.00  --inst_restr_to_given                   false
% 3.04/1.00  --inst_activity_threshold               500
% 3.04/1.00  --inst_out_proof                        true
% 3.04/1.00  
% 3.04/1.00  ------ Resolution Options
% 3.04/1.00  
% 3.04/1.00  --resolution_flag                       false
% 3.04/1.00  --res_lit_sel                           adaptive
% 3.04/1.00  --res_lit_sel_side                      none
% 3.04/1.00  --res_ordering                          kbo
% 3.04/1.00  --res_to_prop_solver                    active
% 3.04/1.00  --res_prop_simpl_new                    false
% 3.04/1.00  --res_prop_simpl_given                  true
% 3.04/1.00  --res_passive_queue_type                priority_queues
% 3.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/1.00  --res_passive_queues_freq               [15;5]
% 3.04/1.00  --res_forward_subs                      full
% 3.04/1.00  --res_backward_subs                     full
% 3.04/1.00  --res_forward_subs_resolution           true
% 3.04/1.00  --res_backward_subs_resolution          true
% 3.04/1.00  --res_orphan_elimination                true
% 3.04/1.00  --res_time_limit                        2.
% 3.04/1.00  --res_out_proof                         true
% 3.04/1.00  
% 3.04/1.00  ------ Superposition Options
% 3.04/1.00  
% 3.04/1.00  --superposition_flag                    true
% 3.04/1.00  --sup_passive_queue_type                priority_queues
% 3.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.04/1.00  --demod_completeness_check              fast
% 3.04/1.00  --demod_use_ground                      true
% 3.04/1.00  --sup_to_prop_solver                    passive
% 3.04/1.00  --sup_prop_simpl_new                    true
% 3.04/1.00  --sup_prop_simpl_given                  true
% 3.04/1.00  --sup_fun_splitting                     false
% 3.04/1.00  --sup_smt_interval                      50000
% 3.04/1.00  
% 3.04/1.00  ------ Superposition Simplification Setup
% 3.04/1.00  
% 3.04/1.00  --sup_indices_passive                   []
% 3.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_full_bw                           [BwDemod]
% 3.04/1.00  --sup_immed_triv                        [TrivRules]
% 3.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_immed_bw_main                     []
% 3.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/1.00  
% 3.04/1.00  ------ Combination Options
% 3.04/1.00  
% 3.04/1.00  --comb_res_mult                         3
% 3.04/1.00  --comb_sup_mult                         2
% 3.04/1.00  --comb_inst_mult                        10
% 3.04/1.00  
% 3.04/1.00  ------ Debug Options
% 3.04/1.00  
% 3.04/1.00  --dbg_backtrace                         false
% 3.04/1.00  --dbg_dump_prop_clauses                 false
% 3.04/1.00  --dbg_dump_prop_clauses_file            -
% 3.04/1.00  --dbg_out_stat                          false
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  ------ Proving...
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  % SZS status Theorem for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  fof(f8,conjecture,(
% 3.04/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f9,negated_conjecture,(
% 3.04/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.04/1.00    inference(negated_conjecture,[],[f8])).
% 3.04/1.00  
% 3.04/1.00  fof(f20,plain,(
% 3.04/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.04/1.00    inference(ennf_transformation,[],[f9])).
% 3.04/1.00  
% 3.04/1.00  fof(f21,plain,(
% 3.04/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.04/1.00    inference(flattening,[],[f20])).
% 3.04/1.00  
% 3.04/1.00  fof(f37,plain,(
% 3.04/1.00    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.04/1.00    inference(nnf_transformation,[],[f21])).
% 3.04/1.00  
% 3.04/1.00  fof(f38,plain,(
% 3.04/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.04/1.00    inference(flattening,[],[f37])).
% 3.04/1.00  
% 3.04/1.00  fof(f39,plain,(
% 3.04/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.04/1.00    inference(rectify,[],[f38])).
% 3.04/1.00  
% 3.04/1.00  fof(f41,plain,(
% 3.04/1.00    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK7 != sK8 & k1_funct_1(X1,sK7) = k1_funct_1(X1,sK8) & r2_hidden(sK8,X0) & r2_hidden(sK7,X0))) )),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f40,plain,(
% 3.04/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3) & r2_hidden(X3,sK5) & r2_hidden(X2,sK5)) | ~v2_funct_1(sK6)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5)) | v2_funct_1(sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6))),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f42,plain,(
% 3.04/1.00    ((sK7 != sK8 & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) & r2_hidden(sK8,sK5) & r2_hidden(sK7,sK5)) | ~v2_funct_1(sK6)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5)) | v2_funct_1(sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6)),
% 3.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f39,f41,f40])).
% 3.04/1.00  
% 3.04/1.00  fof(f72,plain,(
% 3.04/1.00    v1_funct_2(sK6,sK5,sK5)),
% 3.04/1.00    inference(cnf_transformation,[],[f42])).
% 3.04/1.00  
% 3.04/1.00  fof(f7,axiom,(
% 3.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f18,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/1.00    inference(ennf_transformation,[],[f7])).
% 3.04/1.00  
% 3.04/1.00  fof(f19,plain,(
% 3.04/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/1.00    inference(flattening,[],[f18])).
% 3.04/1.00  
% 3.04/1.00  fof(f36,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/1.00    inference(nnf_transformation,[],[f19])).
% 3.04/1.00  
% 3.04/1.00  fof(f65,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f36])).
% 3.04/1.00  
% 3.04/1.00  fof(f73,plain,(
% 3.04/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))),
% 3.04/1.00    inference(cnf_transformation,[],[f42])).
% 3.04/1.00  
% 3.04/1.00  fof(f6,axiom,(
% 3.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f17,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/1.00    inference(ennf_transformation,[],[f6])).
% 3.04/1.00  
% 3.04/1.00  fof(f64,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f17])).
% 3.04/1.00  
% 3.04/1.00  fof(f3,axiom,(
% 3.04/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f11,plain,(
% 3.04/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f3])).
% 3.04/1.00  
% 3.04/1.00  fof(f12,plain,(
% 3.04/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(flattening,[],[f11])).
% 3.04/1.00  
% 3.04/1.00  fof(f24,plain,(
% 3.04/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(nnf_transformation,[],[f12])).
% 3.04/1.00  
% 3.04/1.00  fof(f25,plain,(
% 3.04/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(rectify,[],[f24])).
% 3.04/1.00  
% 3.04/1.00  fof(f26,plain,(
% 3.04/1.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f27,plain,(
% 3.04/1.00    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).
% 3.04/1.00  
% 3.04/1.00  fof(f47,plain,(
% 3.04/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f71,plain,(
% 3.04/1.00    v1_funct_1(sK6)),
% 3.04/1.00    inference(cnf_transformation,[],[f42])).
% 3.04/1.00  
% 3.04/1.00  fof(f1,axiom,(
% 3.04/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f10,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(ennf_transformation,[],[f1])).
% 3.04/1.00  
% 3.04/1.00  fof(f43,plain,(
% 3.04/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f10])).
% 3.04/1.00  
% 3.04/1.00  fof(f2,axiom,(
% 3.04/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f44,plain,(
% 3.04/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f2])).
% 3.04/1.00  
% 3.04/1.00  fof(f46,plain,(
% 3.04/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f48,plain,(
% 3.04/1.00    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f77,plain,(
% 3.04/1.00    k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) | ~v2_funct_1(sK6)),
% 3.04/1.00    inference(cnf_transformation,[],[f42])).
% 3.04/1.00  
% 3.04/1.00  fof(f74,plain,(
% 3.04/1.00    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5) | v2_funct_1(sK6)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f42])).
% 3.04/1.01  
% 3.04/1.01  fof(f49,plain,(
% 3.04/1.01    ( ! [X0] : (v2_funct_1(X0) | sK1(X0) != sK2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/1.01    inference(cnf_transformation,[],[f27])).
% 3.04/1.01  
% 3.04/1.01  fof(f45,plain,(
% 3.04/1.01    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/1.01    inference(cnf_transformation,[],[f27])).
% 3.04/1.01  
% 3.04/1.01  fof(f78,plain,(
% 3.04/1.01    sK7 != sK8 | ~v2_funct_1(sK6)),
% 3.04/1.01    inference(cnf_transformation,[],[f42])).
% 3.04/1.01  
% 3.04/1.01  fof(f75,plain,(
% 3.04/1.01    r2_hidden(sK7,sK5) | ~v2_funct_1(sK6)),
% 3.04/1.01    inference(cnf_transformation,[],[f42])).
% 3.04/1.01  
% 3.04/1.01  fof(f76,plain,(
% 3.04/1.01    r2_hidden(sK8,sK5) | ~v2_funct_1(sK6)),
% 3.04/1.01    inference(cnf_transformation,[],[f42])).
% 3.04/1.01  
% 3.04/1.01  fof(f66,plain,(
% 3.04/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/1.01    inference(cnf_transformation,[],[f36])).
% 3.04/1.01  
% 3.04/1.01  fof(f92,plain,(
% 3.04/1.01    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.04/1.01    inference(equality_resolution,[],[f66])).
% 3.04/1.01  
% 3.04/1.01  cnf(c_34,negated_conjecture,
% 3.04/1.01      ( v1_funct_2(sK6,sK5,sK5) ),
% 3.04/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_27,plain,
% 3.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.04/1.01      | k1_xboole_0 = X2 ),
% 3.04/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_33,negated_conjecture,
% 3.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
% 3.04/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_424,plain,
% 3.04/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK6 != X0
% 3.04/1.01      | k1_xboole_0 = X2 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_425,plain,
% 3.04/1.01      ( ~ v1_funct_2(sK6,X0,X1)
% 3.04/1.01      | k1_relset_1(X0,X1,sK6) = X0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | k1_xboole_0 = X1 ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_424]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_576,plain,
% 3.04/1.01      ( k1_relset_1(X0,X1,sK6) = X0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK5 != X0
% 3.04/1.01      | sK5 != X1
% 3.04/1.01      | sK6 != sK6
% 3.04/1.01      | k1_xboole_0 = X1 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_34,c_425]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_577,plain,
% 3.04/1.01      ( k1_relset_1(sK5,sK5,sK6) = sK5
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | k1_xboole_0 = sK5 ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_576]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_2930,plain,
% 3.04/1.01      ( k1_relset_1(sK5,sK5,sK6) = sK5 | k1_xboole_0 = sK5 ),
% 3.04/1.01      inference(equality_resolution_simp,[status(thm)],[c_577]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5193,plain,
% 3.04/1.01      ( k1_relset_1(sK5,sK5,sK6) = sK5 | k1_xboole_0 = sK5 ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_2930]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_21,plain,
% 3.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_460,plain,
% 3.04/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK6 != X2 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_461,plain,
% 3.04/1.01      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_460]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5196,plain,
% 3.04/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | k1_relset_1(X0_51,X1_51,sK6) = k1_relat_1(sK6) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_461]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6144,plain,
% 3.04/1.01      ( k1_relset_1(sK5,sK5,sK6) = k1_relat_1(sK6) ),
% 3.04/1.01      inference(equality_resolution,[status(thm)],[c_5196]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6268,plain,
% 3.04/1.01      ( k1_relat_1(sK6) = sK5 | sK5 = k1_xboole_0 ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_5193,c_6144]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_4,plain,
% 3.04/1.01      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 3.04/1.01      | ~ v1_funct_1(X0)
% 3.04/1.01      | v2_funct_1(X0)
% 3.04/1.01      | ~ v1_relat_1(X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5220,plain,
% 3.04/1.01      ( r2_hidden(sK2(X0_51),k1_relat_1(X0_51))
% 3.04/1.01      | ~ v1_funct_1(X0_51)
% 3.04/1.01      | v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5764,plain,
% 3.04/1.01      ( r2_hidden(sK2(X0_51),k1_relat_1(X0_51)) = iProver_top
% 3.04/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.04/1.01      | v2_funct_1(X0_51) = iProver_top
% 3.04/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5220]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6507,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK2(sK6),sK5) = iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6268,c_5764]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_35,negated_conjecture,
% 3.04/1.01      ( v1_funct_1(sK6) ),
% 3.04/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_36,plain,
% 3.04/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5226,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6098,plain,
% 3.04/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5226]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_0,plain,
% 3.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/1.01      | ~ v1_relat_1(X1)
% 3.04/1.01      | v1_relat_1(X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_409,plain,
% 3.04/1.01      ( ~ v1_relat_1(X0)
% 3.04/1.01      | v1_relat_1(X1)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0)
% 3.04/1.01      | sK6 != X1 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_33]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_410,plain,
% 3.04/1.01      ( ~ v1_relat_1(X0)
% 3.04/1.01      | v1_relat_1(sK6)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0) ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_409]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5197,plain,
% 3.04/1.01      ( ~ v1_relat_1(X0_51)
% 3.04/1.01      | v1_relat_1(sK6)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(X0_51) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_410]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6093,plain,
% 3.04/1.01      ( ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
% 3.04/1.01      | v1_relat_1(sK6)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5197]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6214,plain,
% 3.04/1.01      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | v1_relat_1(sK6)
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_6093]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6215,plain,
% 3.04/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | v1_relat_1(k2_zfmisc_1(sK5,sK5)) != iProver_top
% 3.04/1.01      | v1_relat_1(sK6) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6214]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_1,plain,
% 3.04/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5223,plain,
% 3.04/1.01      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6246,plain,
% 3.04/1.01      ( v1_relat_1(k2_zfmisc_1(sK5,sK5)) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5223]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6247,plain,
% 3.04/1.01      ( v1_relat_1(k2_zfmisc_1(sK5,sK5)) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6246]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5,plain,
% 3.04/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 3.04/1.01      | ~ v1_funct_1(X0)
% 3.04/1.01      | v2_funct_1(X0)
% 3.04/1.01      | ~ v1_relat_1(X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5219,plain,
% 3.04/1.01      ( r2_hidden(sK1(X0_51),k1_relat_1(X0_51))
% 3.04/1.01      | ~ v1_funct_1(X0_51)
% 3.04/1.01      | v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5765,plain,
% 3.04/1.01      ( r2_hidden(sK1(X0_51),k1_relat_1(X0_51)) = iProver_top
% 3.04/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.04/1.01      | v2_funct_1(X0_51) = iProver_top
% 3.04/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5219]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6569,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK1(sK6),sK5) = iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6268,c_5765]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5199,negated_conjecture,
% 3.04/1.01      ( v1_funct_1(sK6) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_35]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5785,plain,
% 3.04/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5199]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_3,plain,
% 3.04/1.01      ( ~ v1_funct_1(X0)
% 3.04/1.01      | v2_funct_1(X0)
% 3.04/1.01      | ~ v1_relat_1(X0)
% 3.04/1.01      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
% 3.04/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5221,plain,
% 3.04/1.01      ( ~ v1_funct_1(X0_51)
% 3.04/1.01      | v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51)
% 3.04/1.01      | k1_funct_1(X0_51,sK2(X0_51)) = k1_funct_1(X0_51,sK1(X0_51)) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5763,plain,
% 3.04/1.01      ( k1_funct_1(X0_51,sK2(X0_51)) = k1_funct_1(X0_51,sK1(X0_51))
% 3.04/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.04/1.01      | v2_funct_1(X0_51) = iProver_top
% 3.04/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5221]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6480,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_5785,c_5763]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6145,plain,
% 3.04/1.01      ( ~ v1_funct_1(sK6)
% 3.04/1.01      | v2_funct_1(sK6)
% 3.04/1.01      | ~ v1_relat_1(sK6)
% 3.04/1.01      | k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6)) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5221]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6146,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6145]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6633,plain,
% 3.04/1.01      ( v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6)) ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_6480,c_36,c_6098,c_6146,c_6215,c_6247]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6634,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(renaming,[status(thm)],[c_6633]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_29,negated_conjecture,
% 3.04/1.01      ( ~ v2_funct_1(sK6) | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
% 3.04/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5203,negated_conjecture,
% 3.04/1.01      ( ~ v2_funct_1(sK6) | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_29]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5781,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5203]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6639,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK2(sK6)) = k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6634,c_5781]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_32,negated_conjecture,
% 3.04/1.01      ( ~ r2_hidden(X0,sK5)
% 3.04/1.01      | ~ r2_hidden(X1,sK5)
% 3.04/1.01      | v2_funct_1(sK6)
% 3.04/1.01      | X1 = X0
% 3.04/1.01      | k1_funct_1(sK6,X1) != k1_funct_1(sK6,X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5200,negated_conjecture,
% 3.04/1.01      ( ~ r2_hidden(X0_53,sK5)
% 3.04/1.01      | ~ r2_hidden(X1_53,sK5)
% 3.04/1.01      | v2_funct_1(sK6)
% 3.04/1.01      | X1_53 = X0_53
% 3.04/1.01      | k1_funct_1(sK6,X1_53) != k1_funct_1(sK6,X0_53) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_32]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5784,plain,
% 3.04/1.01      ( X0_53 = X1_53
% 3.04/1.01      | k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,X1_53)
% 3.04/1.01      | r2_hidden(X0_53,sK5) != iProver_top
% 3.04/1.01      | r2_hidden(X1_53,sK5) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5200]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6682,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK1(sK6)) != k1_funct_1(sK6,X0_53)
% 3.04/1.01      | k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK2(sK6) = X0_53
% 3.04/1.01      | r2_hidden(X0_53,sK5) != iProver_top
% 3.04/1.01      | r2_hidden(sK2(sK6),sK5) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6639,c_5784]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6741,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK2(sK6) = sK1(sK6)
% 3.04/1.01      | r2_hidden(sK2(sK6),sK5) != iProver_top
% 3.04/1.01      | r2_hidden(sK1(sK6),sK5) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(equality_resolution,[status(thm)],[c_6682]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_2,plain,
% 3.04/1.01      ( ~ v1_funct_1(X0)
% 3.04/1.01      | v2_funct_1(X0)
% 3.04/1.01      | ~ v1_relat_1(X0)
% 3.04/1.01      | sK2(X0) != sK1(X0) ),
% 3.04/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5222,plain,
% 3.04/1.01      ( ~ v1_funct_1(X0_51)
% 3.04/1.01      | v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51)
% 3.04/1.01      | sK2(X0_51) != sK1(X0_51) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6136,plain,
% 3.04/1.01      ( ~ v1_funct_1(sK6)
% 3.04/1.01      | v2_funct_1(sK6)
% 3.04/1.01      | ~ v1_relat_1(sK6)
% 3.04/1.01      | sK2(sK6) != sK1(sK6) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5222]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6137,plain,
% 3.04/1.01      ( sK2(sK6) != sK1(sK6)
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6136]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6442,plain,
% 3.04/1.01      ( ~ r2_hidden(sK2(sK6),sK5)
% 3.04/1.01      | ~ r2_hidden(sK1(sK6),sK5)
% 3.04/1.01      | v2_funct_1(sK6)
% 3.04/1.01      | k1_funct_1(sK6,sK2(sK6)) != k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | sK2(sK6) = sK1(sK6) ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5200]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6443,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK2(sK6)) != k1_funct_1(sK6,sK1(sK6))
% 3.04/1.01      | sK2(sK6) = sK1(sK6)
% 3.04/1.01      | r2_hidden(sK2(sK6),sK5) != iProver_top
% 3.04/1.01      | r2_hidden(sK1(sK6),sK5) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6442]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6863,plain,
% 3.04/1.01      ( r2_hidden(sK2(sK6),sK5) != iProver_top
% 3.04/1.01      | r2_hidden(sK1(sK6),sK5) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_6741,c_36,c_6098,c_6137,c_6146,c_6215,c_6247,c_6443]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6995,plain,
% 3.04/1.01      ( v2_funct_1(sK6) = iProver_top | sK5 = k1_xboole_0 ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_6507,c_36,c_6098,c_6215,c_6247,c_6569,c_6863]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6996,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0 | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(renaming,[status(thm)],[c_6995]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7001,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) | sK5 = k1_xboole_0 ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6996,c_5781]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6,plain,
% 3.04/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.04/1.01      | ~ v1_funct_1(X1)
% 3.04/1.01      | ~ v2_funct_1(X1)
% 3.04/1.01      | ~ v1_relat_1(X1)
% 3.04/1.01      | X0 = X2
% 3.04/1.01      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 3.04/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5218,plain,
% 3.04/1.01      ( ~ r2_hidden(X0_53,k1_relat_1(X0_51))
% 3.04/1.01      | ~ r2_hidden(X1_53,k1_relat_1(X0_51))
% 3.04/1.01      | ~ v1_funct_1(X0_51)
% 3.04/1.01      | ~ v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51)
% 3.04/1.01      | X0_53 = X1_53
% 3.04/1.01      | k1_funct_1(X0_51,X0_53) != k1_funct_1(X0_51,X1_53) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5766,plain,
% 3.04/1.01      ( X0_53 = X1_53
% 3.04/1.01      | k1_funct_1(X0_51,X0_53) != k1_funct_1(X0_51,X1_53)
% 3.04/1.01      | r2_hidden(X1_53,k1_relat_1(X0_51)) != iProver_top
% 3.04/1.01      | r2_hidden(X0_53,k1_relat_1(X0_51)) != iProver_top
% 3.04/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.04/1.01      | v2_funct_1(X0_51) != iProver_top
% 3.04/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5218]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7126,plain,
% 3.04/1.01      ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_7001,c_5766]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7363,plain,
% 3.04/1.01      ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | sK5 = k1_xboole_0
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7) ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_7126,c_36,c_6098,c_6215,c_6247,c_6996]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7364,plain,
% 3.04/1.01      ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top ),
% 3.04/1.01      inference(renaming,[status(thm)],[c_7363]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7376,plain,
% 3.04/1.01      ( sK8 = sK7
% 3.04/1.01      | sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
% 3.04/1.01      inference(equality_resolution,[status(thm)],[c_7364]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_28,negated_conjecture,
% 3.04/1.01      ( ~ v2_funct_1(sK6) | sK7 != sK8 ),
% 3.04/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5204,negated_conjecture,
% 3.04/1.01      ( ~ v2_funct_1(sK6) | sK7 != sK8 ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5300,plain,
% 3.04/1.01      ( sK7 != sK8 | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5204]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5301,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5203]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6619,plain,
% 3.04/1.01      ( ~ r2_hidden(sK8,k1_relat_1(X0_51))
% 3.04/1.01      | ~ r2_hidden(sK7,k1_relat_1(X0_51))
% 3.04/1.01      | ~ v1_funct_1(X0_51)
% 3.04/1.01      | ~ v2_funct_1(X0_51)
% 3.04/1.01      | ~ v1_relat_1(X0_51)
% 3.04/1.01      | k1_funct_1(X0_51,sK7) != k1_funct_1(X0_51,sK8)
% 3.04/1.01      | sK7 = sK8 ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5218]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6977,plain,
% 3.04/1.01      ( ~ r2_hidden(sK8,k1_relat_1(sK6))
% 3.04/1.01      | ~ r2_hidden(sK7,k1_relat_1(sK6))
% 3.04/1.01      | ~ v1_funct_1(sK6)
% 3.04/1.01      | ~ v2_funct_1(sK6)
% 3.04/1.01      | ~ v1_relat_1(sK6)
% 3.04/1.01      | k1_funct_1(sK6,sK7) != k1_funct_1(sK6,sK8)
% 3.04/1.01      | sK7 = sK8 ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_6619]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6978,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,sK8)
% 3.04/1.01      | sK7 = sK8
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_6977]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7453,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_7376,c_36,c_5300,c_5301,c_6098,c_6215,c_6247,c_6978,
% 3.04/1.01                 c_6996]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7460,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK7,sK5) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6268,c_7453]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_31,negated_conjecture,
% 3.04/1.01      ( r2_hidden(sK7,sK5) | ~ v2_funct_1(sK6) ),
% 3.04/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_42,plain,
% 3.04/1.01      ( r2_hidden(sK7,sK5) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7495,plain,
% 3.04/1.01      ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | sK5 = k1_xboole_0 ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_7460,c_42,c_6996]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7496,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top ),
% 3.04/1.01      inference(renaming,[status(thm)],[c_7495]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7501,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK8,sK5) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_6268,c_7496]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_30,negated_conjecture,
% 3.04/1.01      ( r2_hidden(sK8,sK5) | ~ v2_funct_1(sK6) ),
% 3.04/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_43,plain,
% 3.04/1.01      ( r2_hidden(sK8,sK5) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7504,plain,
% 3.04/1.01      ( sK5 = k1_xboole_0 ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_7501,c_43,c_6996]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7509,plain,
% 3.04/1.01      ( r2_hidden(sK2(sK6),k1_xboole_0) != iProver_top
% 3.04/1.01      | r2_hidden(sK1(sK6),k1_xboole_0) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(demodulation,[status(thm)],[c_7504,c_6863]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7512,plain,
% 3.04/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.04/1.01      inference(demodulation,[status(thm)],[c_7504,c_6144]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_26,plain,
% 3.04/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.04/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.04/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_504,plain,
% 3.04/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.04/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK6 != X0 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_505,plain,
% 3.04/1.01      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 3.04/1.01      | k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)) ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_504]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_601,plain,
% 3.04/1.01      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK5 != X0
% 3.04/1.01      | sK5 != k1_xboole_0
% 3.04/1.01      | sK6 != sK6 ),
% 3.04/1.01      inference(resolution_lifted,[status(thm)],[c_34,c_505]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_602,plain,
% 3.04/1.01      ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.04/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | sK5 != k1_xboole_0 ),
% 3.04/1.01      inference(unflattening,[status(thm)],[c_601]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5194,plain,
% 3.04/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))
% 3.04/1.01      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.04/1.01      | sK5 != k1_xboole_0 ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_602]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7516,plain,
% 3.04/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 3.04/1.01      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.04/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.04/1.01      inference(demodulation,[status(thm)],[c_7504,c_5194]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7532,plain,
% 3.04/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.04/1.01      inference(equality_resolution_simp,[status(thm)],[c_7516]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7545,plain,
% 3.04/1.01      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.04/1.01      inference(light_normalisation,[status(thm)],[c_7512,c_7532]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8020,plain,
% 3.04/1.01      ( r2_hidden(sK1(sK6),k1_xboole_0) = iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_7545,c_5765]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8021,plain,
% 3.04/1.01      ( r2_hidden(sK2(sK6),k1_xboole_0) = iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) = iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_7545,c_5764]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8117,plain,
% 3.04/1.01      ( v2_funct_1(sK6) = iProver_top ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_7509,c_36,c_6098,c_6215,c_6247,c_8020,c_8021]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8123,plain,
% 3.04/1.01      ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_8117,c_5781]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8240,plain,
% 3.04/1.01      ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | r2_hidden(X0_53,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(superposition,[status(thm)],[c_8123,c_5766]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8248,plain,
% 3.04/1.01      ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | r2_hidden(X0_53,k1_xboole_0) != iProver_top
% 3.04/1.01      | r2_hidden(sK8,k1_xboole_0) != iProver_top
% 3.04/1.01      | v1_funct_1(sK6) != iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top
% 3.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.04/1.01      inference(light_normalisation,[status(thm)],[c_8240,c_7545]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5202,negated_conjecture,
% 3.04/1.01      ( r2_hidden(sK8,sK5) | ~ v2_funct_1(sK6) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5782,plain,
% 3.04/1.01      ( r2_hidden(sK8,sK5) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5202]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7519,plain,
% 3.04/1.01      ( r2_hidden(sK8,k1_xboole_0) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(demodulation,[status(thm)],[c_7504,c_5782]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8507,plain,
% 3.04/1.01      ( k1_funct_1(sK6,X0_53) != k1_funct_1(sK6,sK7)
% 3.04/1.01      | sK8 = X0_53
% 3.04/1.01      | r2_hidden(X0_53,k1_xboole_0) != iProver_top ),
% 3.04/1.01      inference(global_propositional_subsumption,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_8248,c_36,c_6098,c_6215,c_6247,c_7509,c_7519,c_8020,
% 3.04/1.01                 c_8021]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_8519,plain,
% 3.04/1.01      ( sK8 = sK7 | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.04/1.01      inference(equality_resolution,[status(thm)],[c_8507]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5201,negated_conjecture,
% 3.04/1.01      ( r2_hidden(sK7,sK5) | ~ v2_funct_1(sK6) ),
% 3.04/1.01      inference(subtyping,[status(esa)],[c_31]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5783,plain,
% 3.04/1.01      ( r2_hidden(sK7,sK5) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(predicate_to_equality,[status(thm)],[c_5201]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_7518,plain,
% 3.04/1.01      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 3.04/1.01      | v2_funct_1(sK6) != iProver_top ),
% 3.04/1.01      inference(demodulation,[status(thm)],[c_7504,c_5783]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5230,plain,
% 3.04/1.01      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.04/1.01      theory(equality) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6624,plain,
% 3.04/1.01      ( sK8 != X0_53 | sK7 != X0_53 | sK7 = sK8 ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5230]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_6625,plain,
% 3.04/1.01      ( sK8 != sK7 | sK7 = sK8 | sK7 != sK7 ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_6624]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5227,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.04/1.01  
% 3.04/1.01  cnf(c_5254,plain,
% 3.04/1.01      ( sK7 = sK7 ),
% 3.04/1.01      inference(instantiation,[status(thm)],[c_5227]) ).
% 3.04/1.01  
% 3.04/1.01  cnf(contradiction,plain,
% 3.04/1.01      ( $false ),
% 3.04/1.01      inference(minisat,
% 3.04/1.01                [status(thm)],
% 3.04/1.01                [c_8519,c_8117,c_7518,c_6625,c_5300,c_5254]) ).
% 3.04/1.01  
% 3.04/1.01  
% 3.04/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/1.01  
% 3.04/1.01  ------                               Statistics
% 3.04/1.01  
% 3.04/1.01  ------ General
% 3.04/1.01  
% 3.04/1.01  abstr_ref_over_cycles:                  0
% 3.04/1.01  abstr_ref_under_cycles:                 0
% 3.04/1.01  gc_basic_clause_elim:                   0
% 3.04/1.01  forced_gc_time:                         0
% 3.04/1.01  parsing_time:                           0.014
% 3.04/1.01  unif_index_cands_time:                  0.
% 3.04/1.01  unif_index_add_time:                    0.
% 3.04/1.01  orderings_time:                         0.
% 3.04/1.01  out_proof_time:                         0.016
% 3.04/1.01  total_time:                             0.308
% 3.04/1.01  num_of_symbols:                         57
% 3.04/1.01  num_of_terms:                           4081
% 3.04/1.01  
% 3.04/1.01  ------ Preprocessing
% 3.04/1.01  
% 3.04/1.01  num_of_splits:                          0
% 3.04/1.01  num_of_split_atoms:                     0
% 3.04/1.01  num_of_reused_defs:                     0
% 3.04/1.01  num_eq_ax_congr_red:                    29
% 3.04/1.01  num_of_sem_filtered_clauses:            1
% 3.04/1.01  num_of_subtypes:                        3
% 3.04/1.01  monotx_restored_types:                  1
% 3.04/1.01  sat_num_of_epr_types:                   0
% 3.04/1.01  sat_num_of_non_cyclic_types:            0
% 3.04/1.01  sat_guarded_non_collapsed_types:        1
% 3.04/1.01  num_pure_diseq_elim:                    0
% 3.04/1.01  simp_replaced_by:                       0
% 3.04/1.01  res_preprocessed:                       162
% 3.04/1.01  prep_upred:                             0
% 3.04/1.01  prep_unflattend:                        254
% 3.04/1.01  smt_new_axioms:                         0
% 3.04/1.01  pred_elim_cands:                        5
% 3.04/1.01  pred_elim:                              2
% 3.04/1.01  pred_elim_cl:                           5
% 3.04/1.01  pred_elim_cycles:                       6
% 3.04/1.01  merged_defs:                            0
% 3.04/1.01  merged_defs_ncl:                        0
% 3.04/1.01  bin_hyper_res:                          0
% 3.04/1.01  prep_cycles:                            4
% 3.04/1.01  pred_elim_time:                         0.092
% 3.04/1.01  splitting_time:                         0.
% 3.04/1.01  sem_filter_time:                        0.
% 3.04/1.01  monotx_time:                            0.
% 3.04/1.01  subtype_inf_time:                       0.001
% 3.04/1.01  
% 3.04/1.01  ------ Problem properties
% 3.04/1.01  
% 3.04/1.01  clauses:                                31
% 3.04/1.01  conjectures:                            6
% 3.04/1.01  epr:                                    4
% 3.04/1.01  horn:                                   21
% 3.04/1.01  ground:                                 8
% 3.04/1.01  unary:                                  2
% 3.04/1.01  binary:                                 9
% 3.04/1.01  lits:                                   122
% 3.04/1.01  lits_eq:                                32
% 3.04/1.01  fd_pure:                                0
% 3.04/1.01  fd_pseudo:                              0
% 3.04/1.01  fd_cond:                                0
% 3.04/1.01  fd_pseudo_cond:                         6
% 3.04/1.01  ac_symbols:                             0
% 3.04/1.01  
% 3.04/1.01  ------ Propositional Solver
% 3.04/1.01  
% 3.04/1.01  prop_solver_calls:                      29
% 3.04/1.01  prop_fast_solver_calls:                 2786
% 3.04/1.01  smt_solver_calls:                       0
% 3.04/1.01  smt_fast_solver_calls:                  0
% 3.04/1.01  prop_num_of_clauses:                    1593
% 3.04/1.01  prop_preprocess_simplified:             6113
% 3.04/1.01  prop_fo_subsumed:                       117
% 3.04/1.01  prop_solver_time:                       0.
% 3.04/1.01  smt_solver_time:                        0.
% 3.04/1.01  smt_fast_solver_time:                   0.
% 3.04/1.01  prop_fast_solver_time:                  0.
% 3.04/1.01  prop_unsat_core_time:                   0.
% 3.04/1.01  
% 3.04/1.01  ------ QBF
% 3.04/1.01  
% 3.04/1.01  qbf_q_res:                              0
% 3.04/1.01  qbf_num_tautologies:                    0
% 3.04/1.01  qbf_prep_cycles:                        0
% 3.04/1.01  
% 3.04/1.01  ------ BMC1
% 3.04/1.01  
% 3.04/1.01  bmc1_current_bound:                     -1
% 3.04/1.01  bmc1_last_solved_bound:                 -1
% 3.04/1.01  bmc1_unsat_core_size:                   -1
% 3.04/1.01  bmc1_unsat_core_parents_size:           -1
% 3.04/1.01  bmc1_merge_next_fun:                    0
% 3.04/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.04/1.01  
% 3.04/1.01  ------ Instantiation
% 3.04/1.01  
% 3.04/1.01  inst_num_of_clauses:                    354
% 3.04/1.01  inst_num_in_passive:                    45
% 3.04/1.01  inst_num_in_active:                     249
% 3.04/1.01  inst_num_in_unprocessed:                60
% 3.04/1.01  inst_num_of_loops:                      340
% 3.04/1.01  inst_num_of_learning_restarts:          0
% 3.04/1.01  inst_num_moves_active_passive:          86
% 3.04/1.01  inst_lit_activity:                      0
% 3.04/1.01  inst_lit_activity_moves:                0
% 3.04/1.01  inst_num_tautologies:                   0
% 3.04/1.01  inst_num_prop_implied:                  0
% 3.04/1.01  inst_num_existing_simplified:           0
% 3.04/1.01  inst_num_eq_res_simplified:             0
% 3.04/1.01  inst_num_child_elim:                    0
% 3.04/1.01  inst_num_of_dismatching_blockings:      123
% 3.04/1.01  inst_num_of_non_proper_insts:           381
% 3.04/1.01  inst_num_of_duplicates:                 0
% 3.04/1.01  inst_inst_num_from_inst_to_res:         0
% 3.04/1.01  inst_dismatching_checking_time:         0.
% 3.04/1.01  
% 3.04/1.01  ------ Resolution
% 3.04/1.01  
% 3.04/1.01  res_num_of_clauses:                     0
% 3.04/1.01  res_num_in_passive:                     0
% 3.04/1.01  res_num_in_active:                      0
% 3.04/1.01  res_num_of_loops:                       166
% 3.04/1.01  res_forward_subset_subsumed:            44
% 3.04/1.01  res_backward_subset_subsumed:           0
% 3.04/1.01  res_forward_subsumed:                   0
% 3.04/1.01  res_backward_subsumed:                  0
% 3.04/1.01  res_forward_subsumption_resolution:     28
% 3.04/1.01  res_backward_subsumption_resolution:    0
% 3.04/1.01  res_clause_to_clause_subsumption:       412
% 3.04/1.01  res_orphan_elimination:                 0
% 3.04/1.01  res_tautology_del:                      89
% 3.04/1.01  res_num_eq_res_simplified:              1
% 3.04/1.01  res_num_sel_changes:                    0
% 3.04/1.01  res_moves_from_active_to_pass:          0
% 3.04/1.01  
% 3.04/1.01  ------ Superposition
% 3.04/1.01  
% 3.04/1.01  sup_time_total:                         0.
% 3.04/1.01  sup_time_generating:                    0.
% 3.04/1.01  sup_time_sim_full:                      0.
% 3.04/1.01  sup_time_sim_immed:                     0.
% 3.04/1.01  
% 3.04/1.01  sup_num_of_clauses:                     56
% 3.04/1.01  sup_num_in_active:                      40
% 3.04/1.01  sup_num_in_passive:                     16
% 3.04/1.01  sup_num_of_loops:                       66
% 3.04/1.01  sup_fw_superposition:                   46
% 3.04/1.01  sup_bw_superposition:                   41
% 3.04/1.01  sup_immediate_simplified:               20
% 3.04/1.01  sup_given_eliminated:                   0
% 3.04/1.01  comparisons_done:                       0
% 3.04/1.01  comparisons_avoided:                    9
% 3.04/1.01  
% 3.04/1.01  ------ Simplifications
% 3.04/1.01  
% 3.04/1.01  
% 3.04/1.01  sim_fw_subset_subsumed:                 11
% 3.04/1.01  sim_bw_subset_subsumed:                 13
% 3.04/1.01  sim_fw_subsumed:                        3
% 3.04/1.01  sim_bw_subsumed:                        0
% 3.04/1.01  sim_fw_subsumption_res:                 6
% 3.04/1.01  sim_bw_subsumption_res:                 0
% 3.04/1.01  sim_tautology_del:                      11
% 3.04/1.01  sim_eq_tautology_del:                   21
% 3.04/1.01  sim_eq_res_simp:                        1
% 3.04/1.01  sim_fw_demodulated:                     0
% 3.04/1.01  sim_bw_demodulated:                     20
% 3.04/1.01  sim_light_normalised:                   5
% 3.04/1.01  sim_joinable_taut:                      0
% 3.04/1.01  sim_joinable_simp:                      0
% 3.04/1.01  sim_ac_normalised:                      0
% 3.04/1.01  sim_smt_subsumption:                    0
% 3.04/1.01  
%------------------------------------------------------------------------------
