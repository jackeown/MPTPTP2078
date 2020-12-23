%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:36 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  201 (87428 expanded)
%              Number of clauses        :  157 (25624 expanded)
%              Number of leaves         :   14 (17389 expanded)
%              Depth                    :   35
%              Number of atoms          :  776 (760899 expanded)
%              Number of equality atoms :  465 (315025 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v2_funct_1(X2)
          <=> ! [X3,X4] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  & r2_hidden(X4,X0)
                  & r2_hidden(X3,X0) )
               => X3 = X4 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X5,X6] :
            ( X5 = X6
            | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
            | ~ r2_hidden(X6,X0)
            | ~ r2_hidden(X5,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ? [X3,X4] :
          ( X3 != X4
          & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
          & r2_hidden(X4,X0)
          & r2_hidden(X3,X0) )
     => ( sK5 != sK6
        & k1_funct_1(X2,sK5) = k1_funct_1(X2,sK6)
        & r2_hidden(sK6,X0)
        & r2_hidden(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | v2_funct_1(X2) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ? [X4,X3] :
            ( X3 != X4
            & k1_funct_1(sK4,X3) = k1_funct_1(sK4,X4)
            & r2_hidden(X4,sK2)
            & r2_hidden(X3,sK2) )
        | ~ v2_funct_1(sK4) )
      & ( ! [X6,X5] :
            ( X5 = X6
            | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
            | ~ r2_hidden(X6,sK2)
            | ~ r2_hidden(X5,sK2) )
        | v2_funct_1(sK4) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ( sK5 != sK6
        & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
        & r2_hidden(sK6,sK2)
        & r2_hidden(sK5,sK2) )
      | ~ v2_funct_1(sK4) )
    & ( ! [X5,X6] :
          ( X5 = X6
          | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK2) )
      | v2_funct_1(sK4) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f24,f23])).

fof(f40,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
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

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f26,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK2)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_236,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_237,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_595,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X1
    | sK2 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_237])).

cnf(c_596,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1157,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_596])).

cnf(c_1797,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_1157])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_272,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_273,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_1806,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(X0_47,X1_47,sK4) = k1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_273])).

cnf(c_2232,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_1806])).

cnf(c_2349,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1797,c_2232])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_417,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_418,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1802,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_2079,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_1862,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_1817,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2211,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_281,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_282,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_1805,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_2213,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_2214,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_2545,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_1862,c_2211,c_2214])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1811,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2072,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_2552,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2545,c_2072])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1800,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ r2_hidden(X1_50,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50 ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_1813,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ r2_hidden(X1_50,k1_relat_1(sK4))
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1800])).

cnf(c_2082,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1_50,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_2619,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_2082])).

cnf(c_2794,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2619])).

cnf(c_2813,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_2794])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_404,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_405,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1803,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_2078,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_406,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_2538,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2078,c_406,c_2211,c_2214])).

cnf(c_2717,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_2538])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_430,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_431,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1801,plain,
    ( ~ v1_relat_1(sK4)
    | v2_funct_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_1863,plain,
    ( sK1(sK4) != sK0(sK4)
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1808,negated_conjecture,
    ( ~ r2_hidden(X0_50,sK2)
    | ~ r2_hidden(X1_50,sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,X1_50) != k1_funct_1(sK4,X0_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2247,plain,
    ( ~ r2_hidden(sK1(sK4),sK2)
    | ~ r2_hidden(sK0(sK4),sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2248,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_391,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_392,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_1804,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_2077,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_393,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_2499,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2077,c_393,c_2211,c_2214])).

cnf(c_2718,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_2499])).

cnf(c_2894,plain,
    ( sK3 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2717,c_1862,c_1863,c_2211,c_2214,c_2248,c_2718])).

cnf(c_2901,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2894,c_2072])).

cnf(c_2991,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
    | sK6 = X0_50
    | sK3 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2082])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1819,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1849,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1812,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1851,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_1852,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_2585,plain,
    ( ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2586,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_1831,plain,
    ( ~ r2_hidden(X0_50,X0_47)
    | r2_hidden(X1_50,X1_47)
    | X1_50 != X0_50
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2567,plain,
    ( r2_hidden(X0_50,X0_47)
    | ~ r2_hidden(sK5,sK2)
    | X0_50 != sK5
    | X0_47 != sK2 ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2841,plain,
    ( r2_hidden(sK5,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_2842,plain,
    ( sK5 != sK5
    | k1_relat_1(sK4) != sK2
    | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2841])).

cnf(c_1814,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v2_funct_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1800])).

cnf(c_2081,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_1864,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_2399,plain,
    ( v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_1864,c_2211,c_2214])).

cnf(c_2900,plain,
    ( sK3 = k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2894,c_2399])).

cnf(c_3149,plain,
    ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_28,c_1849,c_1851,c_1852,c_1862,c_1863,c_2211,c_2214,c_2248,c_2349,c_2586,c_2717,c_2718,c_2842,c_2900])).

cnf(c_3150,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3149])).

cnf(c_3155,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK6,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_3150])).

cnf(c_3158,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2813,c_29,c_2894,c_3155])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1807,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3166,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3158,c_1807])).

cnf(c_3167,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3166])).

cnf(c_2075,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(X1_50,sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_2620,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_2075])).

cnf(c_2659,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2620])).

cnf(c_2734,plain,
    ( r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_1862,c_1863,c_2211,c_2214,c_2248])).

cnf(c_3264,plain,
    ( r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3167,c_2734])).

cnf(c_1816,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1846,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_1821,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_2224,plain,
    ( sK2 != X0_47
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2262,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_2263,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_2291,plain,
    ( sK1(sK4) = sK1(sK4) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2319,plain,
    ( sK0(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2257,plain,
    ( r2_hidden(X0_50,X0_47)
    | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | X0_50 != sK0(sK4)
    | X0_47 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2318,plain,
    ( r2_hidden(sK0(sK4),X0_47)
    | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | sK0(sK4) != sK0(sK4)
    | X0_47 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_2393,plain,
    ( ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | r2_hidden(sK0(sK4),sK2)
    | sK0(sK4) != sK0(sK4)
    | sK2 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_2395,plain,
    ( sK0(sK4) != sK0(sK4)
    | sK2 != k1_relat_1(sK4)
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2393])).

cnf(c_2264,plain,
    ( X0_47 != X1_47
    | sK2 != X1_47
    | sK2 = X0_47 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2394,plain,
    ( k1_relat_1(sK4) != X0_47
    | sK2 != X0_47
    | sK2 = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_2397,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | sK2 = k1_relat_1(sK4)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2394])).

cnf(c_2419,plain,
    ( X0_47 != X1_47
    | X0_47 = sK3
    | sK3 != X1_47 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2420,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_3161,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3158,c_2232])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_328,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_329,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_620,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X0
    | sK2 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_329])).

cnf(c_621,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1798,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_621])).

cnf(c_3164,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3158,c_1798])).

cnf(c_3175,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3164,c_3167])).

cnf(c_3176,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3175])).

cnf(c_3180,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3161,c_3167,c_3176])).

cnf(c_2966,plain,
    ( ~ r2_hidden(X0_50,X0_47)
    | r2_hidden(sK1(sK4),sK2)
    | sK1(sK4) != X0_50
    | sK2 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_3213,plain,
    ( ~ r2_hidden(sK1(sK4),X0_47)
    | r2_hidden(sK1(sK4),sK2)
    | sK1(sK4) != sK1(sK4)
    | sK2 != X0_47 ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_3214,plain,
    ( sK1(sK4) != sK1(sK4)
    | sK2 != X0_47
    | r2_hidden(sK1(sK4),X0_47) != iProver_top
    | r2_hidden(sK1(sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3213])).

cnf(c_3216,plain,
    ( sK1(sK4) != sK1(sK4)
    | sK2 != k1_xboole_0
    | r2_hidden(sK1(sK4),sK2) = iProver_top
    | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3214])).

cnf(c_3385,plain,
    ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3180,c_2538])).

cnf(c_3421,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3264,c_29,c_393,c_1846,c_1807,c_1862,c_1863,c_2211,c_2214,c_2248,c_2262,c_2263,c_2291,c_2319,c_2395,c_2397,c_2420,c_2894,c_3155,c_3180,c_3216,c_3385])).

cnf(c_3427,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3421,c_2072])).

cnf(c_3387,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3180,c_2082])).

cnf(c_3493,plain,
    ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | X0_50 = X1_50
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3387,c_29,c_393,c_1846,c_1807,c_1862,c_1863,c_1864,c_2211,c_2214,c_2248,c_2262,c_2263,c_2291,c_2319,c_2395,c_2397,c_2420,c_2894,c_3155,c_3180,c_3216,c_3385])).

cnf(c_3494,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3493])).

cnf(c_3503,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
    | sK6 = X0_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_3494])).

cnf(c_3515,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5)
    | sK6 = sK5
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3503])).

cnf(c_3451,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK5)
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3427,c_2072])).

cnf(c_1810,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2073,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_3269,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3167,c_2073])).

cnf(c_1809,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2074,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_3268,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3167,c_2074])).

cnf(c_1823,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_2580,plain,
    ( sK6 != X0_50
    | sK5 != X0_50
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_2581,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3515,c_3451,c_3421,c_3269,c_3268,c_2581,c_1851,c_1849])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.53/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.02  
% 1.53/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/1.02  
% 1.53/1.02  ------  iProver source info
% 1.53/1.02  
% 1.53/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.53/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/1.02  git: non_committed_changes: false
% 1.53/1.02  git: last_make_outside_of_git: false
% 1.53/1.02  
% 1.53/1.02  ------ 
% 1.53/1.02  
% 1.53/1.02  ------ Input Options
% 1.53/1.02  
% 1.53/1.02  --out_options                           all
% 1.53/1.02  --tptp_safe_out                         true
% 1.53/1.02  --problem_path                          ""
% 1.53/1.02  --include_path                          ""
% 1.53/1.02  --clausifier                            res/vclausify_rel
% 1.53/1.02  --clausifier_options                    --mode clausify
% 1.53/1.02  --stdin                                 false
% 1.53/1.02  --stats_out                             all
% 1.53/1.02  
% 1.53/1.02  ------ General Options
% 1.53/1.02  
% 1.53/1.02  --fof                                   false
% 1.53/1.02  --time_out_real                         305.
% 1.53/1.02  --time_out_virtual                      -1.
% 1.53/1.02  --symbol_type_check                     false
% 1.53/1.02  --clausify_out                          false
% 1.53/1.02  --sig_cnt_out                           false
% 1.53/1.02  --trig_cnt_out                          false
% 1.53/1.02  --trig_cnt_out_tolerance                1.
% 1.53/1.02  --trig_cnt_out_sk_spl                   false
% 1.53/1.02  --abstr_cl_out                          false
% 1.53/1.02  
% 1.53/1.02  ------ Global Options
% 1.53/1.02  
% 1.53/1.02  --schedule                              default
% 1.53/1.02  --add_important_lit                     false
% 1.53/1.02  --prop_solver_per_cl                    1000
% 1.53/1.02  --min_unsat_core                        false
% 1.53/1.02  --soft_assumptions                      false
% 1.53/1.02  --soft_lemma_size                       3
% 1.53/1.02  --prop_impl_unit_size                   0
% 1.53/1.02  --prop_impl_unit                        []
% 1.53/1.02  --share_sel_clauses                     true
% 1.53/1.02  --reset_solvers                         false
% 1.53/1.02  --bc_imp_inh                            [conj_cone]
% 1.53/1.02  --conj_cone_tolerance                   3.
% 1.53/1.02  --extra_neg_conj                        none
% 1.53/1.02  --large_theory_mode                     true
% 1.53/1.02  --prolific_symb_bound                   200
% 1.53/1.02  --lt_threshold                          2000
% 1.53/1.02  --clause_weak_htbl                      true
% 1.53/1.02  --gc_record_bc_elim                     false
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing Options
% 1.53/1.02  
% 1.53/1.02  --preprocessing_flag                    true
% 1.53/1.02  --time_out_prep_mult                    0.1
% 1.53/1.02  --splitting_mode                        input
% 1.53/1.02  --splitting_grd                         true
% 1.53/1.02  --splitting_cvd                         false
% 1.53/1.02  --splitting_cvd_svl                     false
% 1.53/1.02  --splitting_nvd                         32
% 1.53/1.02  --sub_typing                            true
% 1.53/1.02  --prep_gs_sim                           true
% 1.53/1.02  --prep_unflatten                        true
% 1.53/1.02  --prep_res_sim                          true
% 1.53/1.02  --prep_upred                            true
% 1.53/1.02  --prep_sem_filter                       exhaustive
% 1.53/1.02  --prep_sem_filter_out                   false
% 1.53/1.02  --pred_elim                             true
% 1.53/1.02  --res_sim_input                         true
% 1.53/1.02  --eq_ax_congr_red                       true
% 1.53/1.02  --pure_diseq_elim                       true
% 1.53/1.02  --brand_transform                       false
% 1.53/1.02  --non_eq_to_eq                          false
% 1.53/1.02  --prep_def_merge                        true
% 1.53/1.02  --prep_def_merge_prop_impl              false
% 1.53/1.02  --prep_def_merge_mbd                    true
% 1.53/1.02  --prep_def_merge_tr_red                 false
% 1.53/1.02  --prep_def_merge_tr_cl                  false
% 1.53/1.02  --smt_preprocessing                     true
% 1.53/1.02  --smt_ac_axioms                         fast
% 1.53/1.02  --preprocessed_out                      false
% 1.53/1.02  --preprocessed_stats                    false
% 1.53/1.02  
% 1.53/1.02  ------ Abstraction refinement Options
% 1.53/1.02  
% 1.53/1.02  --abstr_ref                             []
% 1.53/1.02  --abstr_ref_prep                        false
% 1.53/1.02  --abstr_ref_until_sat                   false
% 1.53/1.02  --abstr_ref_sig_restrict                funpre
% 1.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/1.02  --abstr_ref_under                       []
% 1.53/1.02  
% 1.53/1.02  ------ SAT Options
% 1.53/1.02  
% 1.53/1.02  --sat_mode                              false
% 1.53/1.02  --sat_fm_restart_options                ""
% 1.53/1.02  --sat_gr_def                            false
% 1.53/1.02  --sat_epr_types                         true
% 1.53/1.02  --sat_non_cyclic_types                  false
% 1.53/1.02  --sat_finite_models                     false
% 1.53/1.02  --sat_fm_lemmas                         false
% 1.53/1.02  --sat_fm_prep                           false
% 1.53/1.02  --sat_fm_uc_incr                        true
% 1.53/1.02  --sat_out_model                         small
% 1.53/1.02  --sat_out_clauses                       false
% 1.53/1.02  
% 1.53/1.02  ------ QBF Options
% 1.53/1.02  
% 1.53/1.02  --qbf_mode                              false
% 1.53/1.02  --qbf_elim_univ                         false
% 1.53/1.02  --qbf_dom_inst                          none
% 1.53/1.02  --qbf_dom_pre_inst                      false
% 1.53/1.02  --qbf_sk_in                             false
% 1.53/1.02  --qbf_pred_elim                         true
% 1.53/1.02  --qbf_split                             512
% 1.53/1.02  
% 1.53/1.02  ------ BMC1 Options
% 1.53/1.02  
% 1.53/1.02  --bmc1_incremental                      false
% 1.53/1.02  --bmc1_axioms                           reachable_all
% 1.53/1.02  --bmc1_min_bound                        0
% 1.53/1.02  --bmc1_max_bound                        -1
% 1.53/1.02  --bmc1_max_bound_default                -1
% 1.53/1.02  --bmc1_symbol_reachability              true
% 1.53/1.02  --bmc1_property_lemmas                  false
% 1.53/1.02  --bmc1_k_induction                      false
% 1.53/1.02  --bmc1_non_equiv_states                 false
% 1.53/1.02  --bmc1_deadlock                         false
% 1.53/1.02  --bmc1_ucm                              false
% 1.53/1.02  --bmc1_add_unsat_core                   none
% 1.53/1.02  --bmc1_unsat_core_children              false
% 1.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/1.02  --bmc1_out_stat                         full
% 1.53/1.02  --bmc1_ground_init                      false
% 1.53/1.02  --bmc1_pre_inst_next_state              false
% 1.53/1.02  --bmc1_pre_inst_state                   false
% 1.53/1.02  --bmc1_pre_inst_reach_state             false
% 1.53/1.02  --bmc1_out_unsat_core                   false
% 1.53/1.02  --bmc1_aig_witness_out                  false
% 1.53/1.02  --bmc1_verbose                          false
% 1.53/1.02  --bmc1_dump_clauses_tptp                false
% 1.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.53/1.02  --bmc1_dump_file                        -
% 1.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.53/1.02  --bmc1_ucm_extend_mode                  1
% 1.53/1.02  --bmc1_ucm_init_mode                    2
% 1.53/1.02  --bmc1_ucm_cone_mode                    none
% 1.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.53/1.02  --bmc1_ucm_relax_model                  4
% 1.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/1.02  --bmc1_ucm_layered_model                none
% 1.53/1.02  --bmc1_ucm_max_lemma_size               10
% 1.53/1.02  
% 1.53/1.02  ------ AIG Options
% 1.53/1.02  
% 1.53/1.02  --aig_mode                              false
% 1.53/1.02  
% 1.53/1.02  ------ Instantiation Options
% 1.53/1.02  
% 1.53/1.02  --instantiation_flag                    true
% 1.53/1.02  --inst_sos_flag                         false
% 1.53/1.02  --inst_sos_phase                        true
% 1.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/1.02  --inst_lit_sel_side                     num_symb
% 1.53/1.02  --inst_solver_per_active                1400
% 1.53/1.02  --inst_solver_calls_frac                1.
% 1.53/1.02  --inst_passive_queue_type               priority_queues
% 1.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/1.02  --inst_passive_queues_freq              [25;2]
% 1.53/1.02  --inst_dismatching                      true
% 1.53/1.02  --inst_eager_unprocessed_to_passive     true
% 1.53/1.02  --inst_prop_sim_given                   true
% 1.53/1.02  --inst_prop_sim_new                     false
% 1.53/1.02  --inst_subs_new                         false
% 1.53/1.02  --inst_eq_res_simp                      false
% 1.53/1.02  --inst_subs_given                       false
% 1.53/1.02  --inst_orphan_elimination               true
% 1.53/1.02  --inst_learning_loop_flag               true
% 1.53/1.02  --inst_learning_start                   3000
% 1.53/1.02  --inst_learning_factor                  2
% 1.53/1.02  --inst_start_prop_sim_after_learn       3
% 1.53/1.02  --inst_sel_renew                        solver
% 1.53/1.02  --inst_lit_activity_flag                true
% 1.53/1.02  --inst_restr_to_given                   false
% 1.53/1.02  --inst_activity_threshold               500
% 1.53/1.02  --inst_out_proof                        true
% 1.53/1.02  
% 1.53/1.02  ------ Resolution Options
% 1.53/1.02  
% 1.53/1.02  --resolution_flag                       true
% 1.53/1.02  --res_lit_sel                           adaptive
% 1.53/1.02  --res_lit_sel_side                      none
% 1.53/1.02  --res_ordering                          kbo
% 1.53/1.02  --res_to_prop_solver                    active
% 1.53/1.02  --res_prop_simpl_new                    false
% 1.53/1.02  --res_prop_simpl_given                  true
% 1.53/1.02  --res_passive_queue_type                priority_queues
% 1.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/1.02  --res_passive_queues_freq               [15;5]
% 1.53/1.02  --res_forward_subs                      full
% 1.53/1.02  --res_backward_subs                     full
% 1.53/1.02  --res_forward_subs_resolution           true
% 1.53/1.02  --res_backward_subs_resolution          true
% 1.53/1.02  --res_orphan_elimination                true
% 1.53/1.02  --res_time_limit                        2.
% 1.53/1.02  --res_out_proof                         true
% 1.53/1.02  
% 1.53/1.02  ------ Superposition Options
% 1.53/1.02  
% 1.53/1.02  --superposition_flag                    true
% 1.53/1.02  --sup_passive_queue_type                priority_queues
% 1.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.53/1.02  --demod_completeness_check              fast
% 1.53/1.02  --demod_use_ground                      true
% 1.53/1.02  --sup_to_prop_solver                    passive
% 1.53/1.02  --sup_prop_simpl_new                    true
% 1.53/1.02  --sup_prop_simpl_given                  true
% 1.53/1.02  --sup_fun_splitting                     false
% 1.53/1.02  --sup_smt_interval                      50000
% 1.53/1.02  
% 1.53/1.02  ------ Superposition Simplification Setup
% 1.53/1.02  
% 1.53/1.02  --sup_indices_passive                   []
% 1.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_full_bw                           [BwDemod]
% 1.53/1.02  --sup_immed_triv                        [TrivRules]
% 1.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_immed_bw_main                     []
% 1.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.02  
% 1.53/1.02  ------ Combination Options
% 1.53/1.02  
% 1.53/1.02  --comb_res_mult                         3
% 1.53/1.02  --comb_sup_mult                         2
% 1.53/1.02  --comb_inst_mult                        10
% 1.53/1.02  
% 1.53/1.02  ------ Debug Options
% 1.53/1.02  
% 1.53/1.02  --dbg_backtrace                         false
% 1.53/1.02  --dbg_dump_prop_clauses                 false
% 1.53/1.02  --dbg_dump_prop_clauses_file            -
% 1.53/1.02  --dbg_out_stat                          false
% 1.53/1.02  ------ Parsing...
% 1.53/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.53/1.02  ------ Proving...
% 1.53/1.02  ------ Problem Properties 
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  clauses                                 17
% 1.53/1.02  conjectures                             6
% 1.53/1.02  EPR                                     5
% 1.53/1.02  Horn                                    11
% 1.53/1.02  unary                                   0
% 1.53/1.02  binary                                  8
% 1.53/1.02  lits                                    48
% 1.53/1.02  lits eq                                 22
% 1.53/1.02  fd_pure                                 0
% 1.53/1.02  fd_pseudo                               0
% 1.53/1.02  fd_cond                                 0
% 1.53/1.02  fd_pseudo_cond                          2
% 1.53/1.02  AC symbols                              0
% 1.53/1.02  
% 1.53/1.02  ------ Schedule dynamic 5 is on 
% 1.53/1.02  
% 1.53/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  ------ 
% 1.53/1.02  Current options:
% 1.53/1.02  ------ 
% 1.53/1.02  
% 1.53/1.02  ------ Input Options
% 1.53/1.02  
% 1.53/1.02  --out_options                           all
% 1.53/1.02  --tptp_safe_out                         true
% 1.53/1.02  --problem_path                          ""
% 1.53/1.02  --include_path                          ""
% 1.53/1.02  --clausifier                            res/vclausify_rel
% 1.53/1.02  --clausifier_options                    --mode clausify
% 1.53/1.02  --stdin                                 false
% 1.53/1.02  --stats_out                             all
% 1.53/1.02  
% 1.53/1.02  ------ General Options
% 1.53/1.02  
% 1.53/1.02  --fof                                   false
% 1.53/1.02  --time_out_real                         305.
% 1.53/1.02  --time_out_virtual                      -1.
% 1.53/1.02  --symbol_type_check                     false
% 1.53/1.02  --clausify_out                          false
% 1.53/1.02  --sig_cnt_out                           false
% 1.53/1.02  --trig_cnt_out                          false
% 1.53/1.02  --trig_cnt_out_tolerance                1.
% 1.53/1.02  --trig_cnt_out_sk_spl                   false
% 1.53/1.02  --abstr_cl_out                          false
% 1.53/1.02  
% 1.53/1.02  ------ Global Options
% 1.53/1.02  
% 1.53/1.02  --schedule                              default
% 1.53/1.02  --add_important_lit                     false
% 1.53/1.02  --prop_solver_per_cl                    1000
% 1.53/1.02  --min_unsat_core                        false
% 1.53/1.02  --soft_assumptions                      false
% 1.53/1.02  --soft_lemma_size                       3
% 1.53/1.02  --prop_impl_unit_size                   0
% 1.53/1.02  --prop_impl_unit                        []
% 1.53/1.02  --share_sel_clauses                     true
% 1.53/1.02  --reset_solvers                         false
% 1.53/1.02  --bc_imp_inh                            [conj_cone]
% 1.53/1.02  --conj_cone_tolerance                   3.
% 1.53/1.02  --extra_neg_conj                        none
% 1.53/1.02  --large_theory_mode                     true
% 1.53/1.02  --prolific_symb_bound                   200
% 1.53/1.02  --lt_threshold                          2000
% 1.53/1.02  --clause_weak_htbl                      true
% 1.53/1.02  --gc_record_bc_elim                     false
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing Options
% 1.53/1.02  
% 1.53/1.02  --preprocessing_flag                    true
% 1.53/1.02  --time_out_prep_mult                    0.1
% 1.53/1.02  --splitting_mode                        input
% 1.53/1.02  --splitting_grd                         true
% 1.53/1.02  --splitting_cvd                         false
% 1.53/1.02  --splitting_cvd_svl                     false
% 1.53/1.02  --splitting_nvd                         32
% 1.53/1.02  --sub_typing                            true
% 1.53/1.02  --prep_gs_sim                           true
% 1.53/1.02  --prep_unflatten                        true
% 1.53/1.02  --prep_res_sim                          true
% 1.53/1.02  --prep_upred                            true
% 1.53/1.02  --prep_sem_filter                       exhaustive
% 1.53/1.02  --prep_sem_filter_out                   false
% 1.53/1.02  --pred_elim                             true
% 1.53/1.02  --res_sim_input                         true
% 1.53/1.02  --eq_ax_congr_red                       true
% 1.53/1.02  --pure_diseq_elim                       true
% 1.53/1.02  --brand_transform                       false
% 1.53/1.02  --non_eq_to_eq                          false
% 1.53/1.02  --prep_def_merge                        true
% 1.53/1.02  --prep_def_merge_prop_impl              false
% 1.53/1.02  --prep_def_merge_mbd                    true
% 1.53/1.02  --prep_def_merge_tr_red                 false
% 1.53/1.02  --prep_def_merge_tr_cl                  false
% 1.53/1.02  --smt_preprocessing                     true
% 1.53/1.02  --smt_ac_axioms                         fast
% 1.53/1.02  --preprocessed_out                      false
% 1.53/1.02  --preprocessed_stats                    false
% 1.53/1.02  
% 1.53/1.02  ------ Abstraction refinement Options
% 1.53/1.02  
% 1.53/1.02  --abstr_ref                             []
% 1.53/1.02  --abstr_ref_prep                        false
% 1.53/1.02  --abstr_ref_until_sat                   false
% 1.53/1.02  --abstr_ref_sig_restrict                funpre
% 1.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/1.02  --abstr_ref_under                       []
% 1.53/1.02  
% 1.53/1.02  ------ SAT Options
% 1.53/1.02  
% 1.53/1.02  --sat_mode                              false
% 1.53/1.02  --sat_fm_restart_options                ""
% 1.53/1.02  --sat_gr_def                            false
% 1.53/1.02  --sat_epr_types                         true
% 1.53/1.02  --sat_non_cyclic_types                  false
% 1.53/1.02  --sat_finite_models                     false
% 1.53/1.02  --sat_fm_lemmas                         false
% 1.53/1.02  --sat_fm_prep                           false
% 1.53/1.02  --sat_fm_uc_incr                        true
% 1.53/1.02  --sat_out_model                         small
% 1.53/1.02  --sat_out_clauses                       false
% 1.53/1.02  
% 1.53/1.02  ------ QBF Options
% 1.53/1.02  
% 1.53/1.02  --qbf_mode                              false
% 1.53/1.02  --qbf_elim_univ                         false
% 1.53/1.02  --qbf_dom_inst                          none
% 1.53/1.02  --qbf_dom_pre_inst                      false
% 1.53/1.02  --qbf_sk_in                             false
% 1.53/1.02  --qbf_pred_elim                         true
% 1.53/1.02  --qbf_split                             512
% 1.53/1.02  
% 1.53/1.02  ------ BMC1 Options
% 1.53/1.02  
% 1.53/1.02  --bmc1_incremental                      false
% 1.53/1.02  --bmc1_axioms                           reachable_all
% 1.53/1.02  --bmc1_min_bound                        0
% 1.53/1.02  --bmc1_max_bound                        -1
% 1.53/1.02  --bmc1_max_bound_default                -1
% 1.53/1.02  --bmc1_symbol_reachability              true
% 1.53/1.02  --bmc1_property_lemmas                  false
% 1.53/1.02  --bmc1_k_induction                      false
% 1.53/1.02  --bmc1_non_equiv_states                 false
% 1.53/1.02  --bmc1_deadlock                         false
% 1.53/1.02  --bmc1_ucm                              false
% 1.53/1.02  --bmc1_add_unsat_core                   none
% 1.53/1.02  --bmc1_unsat_core_children              false
% 1.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/1.02  --bmc1_out_stat                         full
% 1.53/1.02  --bmc1_ground_init                      false
% 1.53/1.02  --bmc1_pre_inst_next_state              false
% 1.53/1.02  --bmc1_pre_inst_state                   false
% 1.53/1.02  --bmc1_pre_inst_reach_state             false
% 1.53/1.02  --bmc1_out_unsat_core                   false
% 1.53/1.02  --bmc1_aig_witness_out                  false
% 1.53/1.02  --bmc1_verbose                          false
% 1.53/1.02  --bmc1_dump_clauses_tptp                false
% 1.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.53/1.02  --bmc1_dump_file                        -
% 1.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.53/1.02  --bmc1_ucm_extend_mode                  1
% 1.53/1.02  --bmc1_ucm_init_mode                    2
% 1.53/1.02  --bmc1_ucm_cone_mode                    none
% 1.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.53/1.02  --bmc1_ucm_relax_model                  4
% 1.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/1.02  --bmc1_ucm_layered_model                none
% 1.53/1.02  --bmc1_ucm_max_lemma_size               10
% 1.53/1.02  
% 1.53/1.02  ------ AIG Options
% 1.53/1.02  
% 1.53/1.02  --aig_mode                              false
% 1.53/1.02  
% 1.53/1.02  ------ Instantiation Options
% 1.53/1.02  
% 1.53/1.02  --instantiation_flag                    true
% 1.53/1.02  --inst_sos_flag                         false
% 1.53/1.02  --inst_sos_phase                        true
% 1.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/1.02  --inst_lit_sel_side                     none
% 1.53/1.02  --inst_solver_per_active                1400
% 1.53/1.02  --inst_solver_calls_frac                1.
% 1.53/1.02  --inst_passive_queue_type               priority_queues
% 1.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/1.02  --inst_passive_queues_freq              [25;2]
% 1.53/1.02  --inst_dismatching                      true
% 1.53/1.02  --inst_eager_unprocessed_to_passive     true
% 1.53/1.02  --inst_prop_sim_given                   true
% 1.53/1.02  --inst_prop_sim_new                     false
% 1.53/1.02  --inst_subs_new                         false
% 1.53/1.02  --inst_eq_res_simp                      false
% 1.53/1.02  --inst_subs_given                       false
% 1.53/1.02  --inst_orphan_elimination               true
% 1.53/1.02  --inst_learning_loop_flag               true
% 1.53/1.02  --inst_learning_start                   3000
% 1.53/1.02  --inst_learning_factor                  2
% 1.53/1.02  --inst_start_prop_sim_after_learn       3
% 1.53/1.02  --inst_sel_renew                        solver
% 1.53/1.02  --inst_lit_activity_flag                true
% 1.53/1.02  --inst_restr_to_given                   false
% 1.53/1.02  --inst_activity_threshold               500
% 1.53/1.02  --inst_out_proof                        true
% 1.53/1.02  
% 1.53/1.02  ------ Resolution Options
% 1.53/1.02  
% 1.53/1.02  --resolution_flag                       false
% 1.53/1.02  --res_lit_sel                           adaptive
% 1.53/1.02  --res_lit_sel_side                      none
% 1.53/1.02  --res_ordering                          kbo
% 1.53/1.02  --res_to_prop_solver                    active
% 1.53/1.02  --res_prop_simpl_new                    false
% 1.53/1.02  --res_prop_simpl_given                  true
% 1.53/1.02  --res_passive_queue_type                priority_queues
% 1.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/1.02  --res_passive_queues_freq               [15;5]
% 1.53/1.02  --res_forward_subs                      full
% 1.53/1.02  --res_backward_subs                     full
% 1.53/1.02  --res_forward_subs_resolution           true
% 1.53/1.02  --res_backward_subs_resolution          true
% 1.53/1.02  --res_orphan_elimination                true
% 1.53/1.02  --res_time_limit                        2.
% 1.53/1.02  --res_out_proof                         true
% 1.53/1.02  
% 1.53/1.02  ------ Superposition Options
% 1.53/1.02  
% 1.53/1.02  --superposition_flag                    true
% 1.53/1.02  --sup_passive_queue_type                priority_queues
% 1.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.53/1.02  --demod_completeness_check              fast
% 1.53/1.02  --demod_use_ground                      true
% 1.53/1.02  --sup_to_prop_solver                    passive
% 1.53/1.02  --sup_prop_simpl_new                    true
% 1.53/1.02  --sup_prop_simpl_given                  true
% 1.53/1.02  --sup_fun_splitting                     false
% 1.53/1.02  --sup_smt_interval                      50000
% 1.53/1.02  
% 1.53/1.02  ------ Superposition Simplification Setup
% 1.53/1.02  
% 1.53/1.02  --sup_indices_passive                   []
% 1.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_full_bw                           [BwDemod]
% 1.53/1.02  --sup_immed_triv                        [TrivRules]
% 1.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_immed_bw_main                     []
% 1.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.02  
% 1.53/1.02  ------ Combination Options
% 1.53/1.02  
% 1.53/1.02  --comb_res_mult                         3
% 1.53/1.02  --comb_sup_mult                         2
% 1.53/1.02  --comb_inst_mult                        10
% 1.53/1.02  
% 1.53/1.02  ------ Debug Options
% 1.53/1.02  
% 1.53/1.02  --dbg_backtrace                         false
% 1.53/1.02  --dbg_dump_prop_clauses                 false
% 1.53/1.02  --dbg_dump_prop_clauses_file            -
% 1.53/1.02  --dbg_out_stat                          false
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  ------ Proving...
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  % SZS status Theorem for theBenchmark.p
% 1.53/1.02  
% 1.53/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.53/1.02  
% 1.53/1.02  fof(f5,conjecture,(
% 1.53/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f6,negated_conjecture,(
% 1.53/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.53/1.02    inference(negated_conjecture,[],[f5])).
% 1.53/1.02  
% 1.53/1.02  fof(f13,plain,(
% 1.53/1.02    ? [X0,X1,X2] : (((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/1.02    inference(ennf_transformation,[],[f6])).
% 1.53/1.02  
% 1.53/1.02  fof(f14,plain,(
% 1.53/1.02    ? [X0,X1,X2] : ((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/1.02    inference(flattening,[],[f13])).
% 1.53/1.02  
% 1.53/1.02  fof(f20,plain,(
% 1.53/1.02    ? [X0,X1,X2] : (((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/1.02    inference(nnf_transformation,[],[f14])).
% 1.53/1.02  
% 1.53/1.02  fof(f21,plain,(
% 1.53/1.02    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/1.02    inference(flattening,[],[f20])).
% 1.53/1.02  
% 1.53/1.02  fof(f22,plain,(
% 1.53/1.02    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/1.02    inference(rectify,[],[f21])).
% 1.53/1.02  
% 1.53/1.02  fof(f24,plain,(
% 1.53/1.02    ( ! [X2,X0] : (? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => (sK5 != sK6 & k1_funct_1(X2,sK5) = k1_funct_1(X2,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 1.53/1.02    introduced(choice_axiom,[])).
% 1.53/1.02  
% 1.53/1.02  fof(f23,plain,(
% 1.53/1.02    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((? [X4,X3] : (X3 != X4 & k1_funct_1(sK4,X3) = k1_funct_1(sK4,X4) & r2_hidden(X4,sK2) & r2_hidden(X3,sK2)) | ~v2_funct_1(sK4)) & (! [X6,X5] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2)) | v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 1.53/1.02    introduced(choice_axiom,[])).
% 1.53/1.02  
% 1.53/1.02  fof(f25,plain,(
% 1.53/1.02    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK2) & r2_hidden(sK5,sK2)) | ~v2_funct_1(sK4)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2)) | v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 1.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f24,f23])).
% 1.53/1.02  
% 1.53/1.02  fof(f40,plain,(
% 1.53/1.02    v1_funct_2(sK4,sK2,sK3)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f4,axiom,(
% 1.53/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f11,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/1.02    inference(ennf_transformation,[],[f4])).
% 1.53/1.02  
% 1.53/1.02  fof(f12,plain,(
% 1.53/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/1.02    inference(flattening,[],[f11])).
% 1.53/1.02  
% 1.53/1.02  fof(f19,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/1.02    inference(nnf_transformation,[],[f12])).
% 1.53/1.02  
% 1.53/1.02  fof(f33,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/1.02    inference(cnf_transformation,[],[f19])).
% 1.53/1.02  
% 1.53/1.02  fof(f41,plain,(
% 1.53/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f3,axiom,(
% 1.53/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f10,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/1.02    inference(ennf_transformation,[],[f3])).
% 1.53/1.02  
% 1.53/1.02  fof(f32,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/1.02    inference(cnf_transformation,[],[f10])).
% 1.53/1.02  
% 1.53/1.02  fof(f1,axiom,(
% 1.53/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f7,plain,(
% 1.53/1.02    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/1.02    inference(ennf_transformation,[],[f1])).
% 1.53/1.02  
% 1.53/1.02  fof(f8,plain,(
% 1.53/1.02    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/1.02    inference(flattening,[],[f7])).
% 1.53/1.02  
% 1.53/1.02  fof(f15,plain,(
% 1.53/1.02    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/1.02    inference(nnf_transformation,[],[f8])).
% 1.53/1.02  
% 1.53/1.02  fof(f16,plain,(
% 1.53/1.02    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/1.02    inference(rectify,[],[f15])).
% 1.53/1.02  
% 1.53/1.02  fof(f17,plain,(
% 1.53/1.02    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.53/1.02    introduced(choice_axiom,[])).
% 1.53/1.02  
% 1.53/1.02  fof(f18,plain,(
% 1.53/1.02    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.53/1.02  
% 1.53/1.02  fof(f29,plain,(
% 1.53/1.02    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f18])).
% 1.53/1.02  
% 1.53/1.02  fof(f39,plain,(
% 1.53/1.02    v1_funct_1(sK4)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f2,axiom,(
% 1.53/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f9,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/1.02    inference(ennf_transformation,[],[f2])).
% 1.53/1.02  
% 1.53/1.02  fof(f31,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/1.02    inference(cnf_transformation,[],[f9])).
% 1.53/1.02  
% 1.53/1.02  fof(f46,plain,(
% 1.53/1.02    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f26,plain,(
% 1.53/1.02    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f18])).
% 1.53/1.02  
% 1.53/1.02  fof(f45,plain,(
% 1.53/1.02    r2_hidden(sK6,sK2) | ~v2_funct_1(sK4)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f28,plain,(
% 1.53/1.02    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f18])).
% 1.53/1.02  
% 1.53/1.02  fof(f30,plain,(
% 1.53/1.02    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f18])).
% 1.53/1.02  
% 1.53/1.02  fof(f43,plain,(
% 1.53/1.02    ( ! [X6,X5] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2) | v2_funct_1(sK4)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f27,plain,(
% 1.53/1.02    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f18])).
% 1.53/1.02  
% 1.53/1.02  fof(f44,plain,(
% 1.53/1.02    r2_hidden(sK5,sK2) | ~v2_funct_1(sK4)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f47,plain,(
% 1.53/1.02    sK5 != sK6 | ~v2_funct_1(sK4)),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f42,plain,(
% 1.53/1.02    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 1.53/1.02    inference(cnf_transformation,[],[f25])).
% 1.53/1.02  
% 1.53/1.02  fof(f34,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/1.02    inference(cnf_transformation,[],[f19])).
% 1.53/1.02  
% 1.53/1.02  fof(f52,plain,(
% 1.53/1.02    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.53/1.02    inference(equality_resolution,[],[f34])).
% 1.53/1.02  
% 1.53/1.02  cnf(c_20,negated_conjecture,
% 1.53/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 1.53/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_12,plain,
% 1.53/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.53/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.53/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.53/1.02      | k1_xboole_0 = X2 ),
% 1.53/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_19,negated_conjecture,
% 1.53/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.53/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_236,plain,
% 1.53/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.53/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK4 != X0
% 1.53/1.02      | k1_xboole_0 = X2 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_237,plain,
% 1.53/1.02      ( ~ v1_funct_2(sK4,X0,X1)
% 1.53/1.02      | k1_relset_1(X0,X1,sK4) = X0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | k1_xboole_0 = X1 ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_236]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_595,plain,
% 1.53/1.02      ( k1_relset_1(X0,X1,sK4) = X0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK3 != X1
% 1.53/1.02      | sK2 != X0
% 1.53/1.02      | sK4 != sK4
% 1.53/1.02      | k1_xboole_0 = X1 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_237]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_596,plain,
% 1.53/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | k1_xboole_0 = sK3 ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_595]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1157,plain,
% 1.53/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 1.53/1.02      inference(equality_resolution_simp,[status(thm)],[c_596]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1797,plain,
% 1.53/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_1157]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_6,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.53/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_272,plain,
% 1.53/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK4 != X2 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_273,plain,
% 1.53/1.02      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_272]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1806,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | k1_relset_1(X0_47,X1_47,sK4) = k1_relat_1(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_273]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2232,plain,
% 1.53/1.02      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 1.53/1.02      inference(equality_resolution,[status(thm)],[c_1806]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2349,plain,
% 1.53/1.02      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1797,c_2232]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1,plain,
% 1.53/1.02      ( ~ v1_relat_1(X0)
% 1.53/1.02      | ~ v1_funct_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 1.53/1.02      inference(cnf_transformation,[],[f29]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_21,negated_conjecture,
% 1.53/1.02      ( v1_funct_1(sK4) ),
% 1.53/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_417,plain,
% 1.53/1.02      ( ~ v1_relat_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_418,plain,
% 1.53/1.02      ( ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4)
% 1.53/1.02      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_417]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1802,plain,
% 1.53/1.02      ( ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4)
% 1.53/1.02      | k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_418]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2079,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1862,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1817,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2211,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1817]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.53/1.02      | v1_relat_1(X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_281,plain,
% 1.53/1.02      ( v1_relat_1(X0)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_282,plain,
% 1.53/1.02      ( v1_relat_1(sK4)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_281]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1805,plain,
% 1.53/1.02      ( v1_relat_1(sK4)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_282]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2213,plain,
% 1.53/1.02      ( v1_relat_1(sK4)
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1805]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2214,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | v1_relat_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2545,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2079,c_1862,c_2211,c_2214]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_14,negated_conjecture,
% 1.53/1.02      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.53/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1811,negated_conjecture,
% 1.53/1.02      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2072,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2552,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 1.53/1.02      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2545,c_2072]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4,plain,
% 1.53/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.53/1.02      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.53/1.02      | ~ v1_relat_1(X1)
% 1.53/1.02      | ~ v1_funct_1(X1)
% 1.53/1.02      | ~ v2_funct_1(X1)
% 1.53/1.02      | X0 = X2
% 1.53/1.02      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.53/1.02      inference(cnf_transformation,[],[f26]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_443,plain,
% 1.53/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.53/1.02      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.53/1.02      | ~ v1_relat_1(X1)
% 1.53/1.02      | ~ v2_funct_1(X1)
% 1.53/1.02      | X2 = X0
% 1.53/1.02      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.53/1.02      | sK4 != X1 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_444,plain,
% 1.53/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.53/1.02      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | ~ v2_funct_1(sK4)
% 1.53/1.02      | X0 = X1
% 1.53/1.02      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_443]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1800,plain,
% 1.53/1.02      ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
% 1.53/1.02      | ~ r2_hidden(X1_50,k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | ~ v2_funct_1(sK4)
% 1.53/1.02      | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_444]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1813,plain,
% 1.53/1.02      ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
% 1.53/1.02      | ~ r2_hidden(X1_50,k1_relat_1(sK4))
% 1.53/1.02      | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | ~ sP0_iProver_split ),
% 1.53/1.02      inference(splitting,
% 1.53/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.53/1.02                [c_1800]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2082,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(X1_50,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2619,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
% 1.53/1.02      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK1(sK4) = X0_50
% 1.53/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2552,c_2082]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2794,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK1(sK4) = sK0(sK4)
% 1.53/1.02      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(equality_resolution,[status(thm)],[c_2619]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2813,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK1(sK4) = sK0(sK4)
% 1.53/1.02      | sK3 = k1_xboole_0
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2349,c_2794]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_15,negated_conjecture,
% 1.53/1.02      ( r2_hidden(sK6,sK2) | ~ v2_funct_1(sK4) ),
% 1.53/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_29,plain,
% 1.53/1.02      ( r2_hidden(sK6,sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2,plain,
% 1.53/1.02      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.53/1.02      | ~ v1_relat_1(X0)
% 1.53/1.02      | ~ v1_funct_1(X0)
% 1.53/1.02      | v2_funct_1(X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f28]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_404,plain,
% 1.53/1.02      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.53/1.02      | ~ v1_relat_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_405,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_404]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1803,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_405]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2078,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_406,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2538,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2078,c_406,c_2211,c_2214]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2717,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2349,c_2538]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_0,plain,
% 1.53/1.02      ( ~ v1_relat_1(X0)
% 1.53/1.02      | ~ v1_funct_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | sK1(X0) != sK0(X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f30]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_430,plain,
% 1.53/1.02      ( ~ v1_relat_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | sK1(X0) != sK0(X0)
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_431,plain,
% 1.53/1.02      ( ~ v1_relat_1(sK4) | v2_funct_1(sK4) | sK1(sK4) != sK0(sK4) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_430]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1801,plain,
% 1.53/1.02      ( ~ v1_relat_1(sK4) | v2_funct_1(sK4) | sK1(sK4) != sK0(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_431]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1863,plain,
% 1.53/1.02      ( sK1(sK4) != sK0(sK4)
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_17,negated_conjecture,
% 1.53/1.02      ( ~ r2_hidden(X0,sK2)
% 1.53/1.02      | ~ r2_hidden(X1,sK2)
% 1.53/1.02      | v2_funct_1(sK4)
% 1.53/1.02      | X1 = X0
% 1.53/1.02      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1808,negated_conjecture,
% 1.53/1.02      ( ~ r2_hidden(X0_50,sK2)
% 1.53/1.02      | ~ r2_hidden(X1_50,sK2)
% 1.53/1.02      | v2_funct_1(sK4)
% 1.53/1.02      | k1_funct_1(sK4,X1_50) != k1_funct_1(sK4,X0_50)
% 1.53/1.02      | X1_50 = X0_50 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2247,plain,
% 1.53/1.02      ( ~ r2_hidden(sK1(sK4),sK2)
% 1.53/1.02      | ~ r2_hidden(sK0(sK4),sK2)
% 1.53/1.02      | v2_funct_1(sK4)
% 1.53/1.02      | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
% 1.53/1.02      | sK1(sK4) = sK0(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1808]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2248,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
% 1.53/1.02      | sK1(sK4) = sK0(sK4)
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_2247]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3,plain,
% 1.53/1.02      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.53/1.02      | ~ v1_relat_1(X0)
% 1.53/1.02      | ~ v1_funct_1(X0)
% 1.53/1.02      | v2_funct_1(X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f27]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_391,plain,
% 1.53/1.02      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.53/1.02      | ~ v1_relat_1(X0)
% 1.53/1.02      | v2_funct_1(X0)
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_392,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_391]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1804,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.53/1.02      | ~ v1_relat_1(sK4)
% 1.53/1.02      | v2_funct_1(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_392]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2077,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_393,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2499,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2077,c_393,c_2211,c_2214]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2718,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2349,c_2499]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2894,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0 | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2717,c_1862,c_1863,c_2211,c_2214,c_2248,c_2718]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2901,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) | sK3 = k1_xboole_0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2894,c_2072]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2991,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK6 = X0_50
% 1.53/1.02      | sK3 = k1_xboole_0
% 1.53/1.02      | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2901,c_2082]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_16,negated_conjecture,
% 1.53/1.02      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 1.53/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_28,plain,
% 1.53/1.02      ( r2_hidden(sK5,sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1819,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1849,plain,
% 1.53/1.02      ( sK5 = sK5 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1819]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_13,negated_conjecture,
% 1.53/1.02      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.53/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1812,negated_conjecture,
% 1.53/1.02      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1851,plain,
% 1.53/1.02      ( sK5 != sK6 | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1852,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2585,plain,
% 1.53/1.02      ( ~ r2_hidden(sK6,k1_relat_1(sK4))
% 1.53/1.02      | ~ r2_hidden(sK5,k1_relat_1(sK4))
% 1.53/1.02      | ~ sP0_iProver_split
% 1.53/1.02      | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.53/1.02      | sK5 = sK6 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1813]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2586,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.53/1.02      | sK5 = sK6
% 1.53/1.02      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1831,plain,
% 1.53/1.02      ( ~ r2_hidden(X0_50,X0_47)
% 1.53/1.02      | r2_hidden(X1_50,X1_47)
% 1.53/1.02      | X1_50 != X0_50
% 1.53/1.02      | X1_47 != X0_47 ),
% 1.53/1.02      theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2567,plain,
% 1.53/1.02      ( r2_hidden(X0_50,X0_47)
% 1.53/1.02      | ~ r2_hidden(sK5,sK2)
% 1.53/1.02      | X0_50 != sK5
% 1.53/1.02      | X0_47 != sK2 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1831]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2841,plain,
% 1.53/1.02      ( r2_hidden(sK5,k1_relat_1(sK4))
% 1.53/1.02      | ~ r2_hidden(sK5,sK2)
% 1.53/1.02      | sK5 != sK5
% 1.53/1.02      | k1_relat_1(sK4) != sK2 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2567]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2842,plain,
% 1.53/1.02      ( sK5 != sK5
% 1.53/1.02      | k1_relat_1(sK4) != sK2
% 1.53/1.02      | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
% 1.53/1.02      | r2_hidden(sK5,sK2) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_2841]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1814,plain,
% 1.53/1.02      ( ~ v1_relat_1(sK4) | ~ v2_funct_1(sK4) | sP0_iProver_split ),
% 1.53/1.02      inference(splitting,
% 1.53/1.02                [splitting(split),new_symbols(definition,[])],
% 1.53/1.02                [c_1800]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2081,plain,
% 1.53/1.02      ( v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top
% 1.53/1.02      | sP0_iProver_split = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1864,plain,
% 1.53/1.02      ( v1_relat_1(sK4) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top
% 1.53/1.02      | sP0_iProver_split = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2399,plain,
% 1.53/1.02      ( v2_funct_1(sK4) != iProver_top
% 1.53/1.02      | sP0_iProver_split = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2081,c_1864,c_2211,c_2214]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2900,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0 | sP0_iProver_split = iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2894,c_2399]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3149,plain,
% 1.53/1.02      ( r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | sK3 = k1_xboole_0 ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2991,c_28,c_1849,c_1851,c_1852,c_1862,c_1863,c_2211,
% 1.53/1.02                 c_2214,c_2248,c_2349,c_2586,c_2717,c_2718,c_2842,c_2900]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3150,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0
% 1.53/1.02      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top ),
% 1.53/1.02      inference(renaming,[status(thm)],[c_3149]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3155,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0 | r2_hidden(sK6,sK2) != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2349,c_3150]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3158,plain,
% 1.53/1.02      ( sK3 = k1_xboole_0 ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2813,c_29,c_2894,c_3155]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_18,negated_conjecture,
% 1.53/1.02      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 1.53/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1807,negated_conjecture,
% 1.53/1.02      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3166,plain,
% 1.53/1.02      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3158,c_1807]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3167,plain,
% 1.53/1.02      ( sK2 = k1_xboole_0 ),
% 1.53/1.02      inference(equality_resolution_simp,[status(thm)],[c_3166]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2075,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | r2_hidden(X0_50,sK2) != iProver_top
% 1.53/1.02      | r2_hidden(X1_50,sK2) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2620,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
% 1.53/1.02      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK1(sK4) = X0_50
% 1.53/1.02      | r2_hidden(X0_50,sK2) != iProver_top
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2552,c_2075]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2659,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK1(sK4) = sK0(sK4)
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(equality_resolution,[status(thm)],[c_2620]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2734,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_2659,c_1862,c_1863,c_2211,c_2214,c_2248]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3264,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3167,c_2734]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1816,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1846,plain,
% 1.53/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1816]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1821,plain,
% 1.53/1.02      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.53/1.02      theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2224,plain,
% 1.53/1.02      ( sK2 != X0_47 | sK2 = k1_xboole_0 | k1_xboole_0 != X0_47 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2262,plain,
% 1.53/1.02      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2224]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2263,plain,
% 1.53/1.02      ( sK2 = sK2 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1816]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2291,plain,
% 1.53/1.02      ( sK1(sK4) = sK1(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1819]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2319,plain,
% 1.53/1.02      ( sK0(sK4) = sK0(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1819]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2257,plain,
% 1.53/1.02      ( r2_hidden(X0_50,X0_47)
% 1.53/1.02      | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.53/1.02      | X0_50 != sK0(sK4)
% 1.53/1.02      | X0_47 != k1_relat_1(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1831]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2318,plain,
% 1.53/1.02      ( r2_hidden(sK0(sK4),X0_47)
% 1.53/1.02      | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.53/1.02      | sK0(sK4) != sK0(sK4)
% 1.53/1.02      | X0_47 != k1_relat_1(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2257]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2393,plain,
% 1.53/1.02      ( ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2)
% 1.53/1.02      | sK0(sK4) != sK0(sK4)
% 1.53/1.02      | sK2 != k1_relat_1(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2318]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2395,plain,
% 1.53/1.02      ( sK0(sK4) != sK0(sK4)
% 1.53/1.02      | sK2 != k1_relat_1(sK4)
% 1.53/1.02      | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
% 1.53/1.02      | r2_hidden(sK0(sK4),sK2) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_2393]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2264,plain,
% 1.53/1.02      ( X0_47 != X1_47 | sK2 != X1_47 | sK2 = X0_47 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2394,plain,
% 1.53/1.02      ( k1_relat_1(sK4) != X0_47 | sK2 != X0_47 | sK2 = k1_relat_1(sK4) ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2264]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2397,plain,
% 1.53/1.02      ( k1_relat_1(sK4) != k1_xboole_0
% 1.53/1.02      | sK2 = k1_relat_1(sK4)
% 1.53/1.02      | sK2 != k1_xboole_0 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2394]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2419,plain,
% 1.53/1.02      ( X0_47 != X1_47 | X0_47 = sK3 | sK3 != X1_47 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2420,plain,
% 1.53/1.02      ( sK3 != k1_xboole_0
% 1.53/1.02      | k1_xboole_0 = sK3
% 1.53/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2419]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3161,plain,
% 1.53/1.02      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3158,c_2232]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_11,plain,
% 1.53/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.53/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.53/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_328,plain,
% 1.53/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.53/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK4 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_329,plain,
% 1.53/1.02      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 1.53/1.02      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_328]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_620,plain,
% 1.53/1.02      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK3 != X0
% 1.53/1.02      | sK2 != k1_xboole_0
% 1.53/1.02      | sK4 != sK4 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_329]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_621,plain,
% 1.53/1.02      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 1.53/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | sK2 != k1_xboole_0 ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_620]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1798,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.53/1.02      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 1.53/1.02      | sK2 != k1_xboole_0 ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_621]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3164,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.53/1.02      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.53/1.02      | sK2 != k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3158,c_1798]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3175,plain,
% 1.53/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.53/1.02      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.53/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_3164,c_3167]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3176,plain,
% 1.53/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 1.53/1.02      inference(equality_resolution_simp,[status(thm)],[c_3175]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3180,plain,
% 1.53/1.02      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_3161,c_3167,c_3176]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2966,plain,
% 1.53/1.02      ( ~ r2_hidden(X0_50,X0_47)
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2)
% 1.53/1.02      | sK1(sK4) != X0_50
% 1.53/1.02      | sK2 != X0_47 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1831]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3213,plain,
% 1.53/1.02      ( ~ r2_hidden(sK1(sK4),X0_47)
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2)
% 1.53/1.02      | sK1(sK4) != sK1(sK4)
% 1.53/1.02      | sK2 != X0_47 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2966]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3214,plain,
% 1.53/1.02      ( sK1(sK4) != sK1(sK4)
% 1.53/1.02      | sK2 != X0_47
% 1.53/1.02      | r2_hidden(sK1(sK4),X0_47) != iProver_top
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_3213]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3216,plain,
% 1.53/1.02      ( sK1(sK4) != sK1(sK4)
% 1.53/1.02      | sK2 != k1_xboole_0
% 1.53/1.02      | r2_hidden(sK1(sK4),sK2) = iProver_top
% 1.53/1.02      | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_3214]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3385,plain,
% 1.53/1.02      ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3180,c_2538]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3421,plain,
% 1.53/1.02      ( v2_funct_1(sK4) = iProver_top ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_3264,c_29,c_393,c_1846,c_1807,c_1862,c_1863,c_2211,
% 1.53/1.02                 c_2214,c_2248,c_2262,c_2263,c_2291,c_2319,c_2395,c_2397,
% 1.53/1.02                 c_2420,c_2894,c_3155,c_3180,c_3216,c_3385]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3427,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3421,c_2072]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3387,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | r2_hidden(X1_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | sP0_iProver_split != iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3180,c_2082]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3493,plain,
% 1.53/1.02      ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(X1_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50) ),
% 1.53/1.02      inference(global_propositional_subsumption,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_3387,c_29,c_393,c_1846,c_1807,c_1862,c_1863,c_1864,
% 1.53/1.02                 c_2211,c_2214,c_2248,c_2262,c_2263,c_2291,c_2319,c_2395,
% 1.53/1.02                 c_2397,c_2420,c_2894,c_3155,c_3180,c_3216,c_3385]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3494,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
% 1.53/1.02      | X0_50 = X1_50
% 1.53/1.02      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(X1_50,k1_xboole_0) != iProver_top ),
% 1.53/1.02      inference(renaming,[status(thm)],[c_3493]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3503,plain,
% 1.53/1.02      ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK6 = X0_50
% 1.53/1.02      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3427,c_3494]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3515,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5)
% 1.53/1.02      | sK6 = sK5
% 1.53/1.02      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 1.53/1.02      | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_3503]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3451,plain,
% 1.53/1.02      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK5)
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3427,c_2072]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1810,negated_conjecture,
% 1.53/1.02      ( r2_hidden(sK6,sK2) | ~ v2_funct_1(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2073,plain,
% 1.53/1.02      ( r2_hidden(sK6,sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3269,plain,
% 1.53/1.02      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3167,c_2073]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1809,negated_conjecture,
% 1.53/1.02      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 1.53/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2074,plain,
% 1.53/1.02      ( r2_hidden(sK5,sK2) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1809]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3268,plain,
% 1.53/1.02      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 1.53/1.02      | v2_funct_1(sK4) != iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_3167,c_2074]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1823,plain,
% 1.53/1.02      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 1.53/1.02      theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2580,plain,
% 1.53/1.02      ( sK6 != X0_50 | sK5 != X0_50 | sK5 = sK6 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_1823]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2581,plain,
% 1.53/1.02      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 1.53/1.02      inference(instantiation,[status(thm)],[c_2580]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(contradiction,plain,
% 1.53/1.02      ( $false ),
% 1.53/1.02      inference(minisat,
% 1.53/1.02                [status(thm)],
% 1.53/1.02                [c_3515,c_3451,c_3421,c_3269,c_3268,c_2581,c_1851,c_1849]) ).
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.53/1.02  
% 1.53/1.02  ------                               Statistics
% 1.53/1.02  
% 1.53/1.02  ------ General
% 1.53/1.02  
% 1.53/1.02  abstr_ref_over_cycles:                  0
% 1.53/1.02  abstr_ref_under_cycles:                 0
% 1.53/1.02  gc_basic_clause_elim:                   0
% 1.53/1.02  forced_gc_time:                         0
% 1.53/1.02  parsing_time:                           0.028
% 1.53/1.02  unif_index_cands_time:                  0.
% 1.53/1.02  unif_index_add_time:                    0.
% 1.53/1.02  orderings_time:                         0.
% 1.53/1.02  out_proof_time:                         0.042
% 1.53/1.02  total_time:                             0.213
% 1.53/1.02  num_of_symbols:                         53
% 1.53/1.02  num_of_terms:                           1481
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing
% 1.53/1.02  
% 1.53/1.02  num_of_splits:                          1
% 1.53/1.02  num_of_split_atoms:                     1
% 1.53/1.02  num_of_reused_defs:                     0
% 1.53/1.02  num_eq_ax_congr_red:                    6
% 1.53/1.02  num_of_sem_filtered_clauses:            1
% 1.53/1.02  num_of_subtypes:                        5
% 1.53/1.02  monotx_restored_types:                  0
% 1.53/1.02  sat_num_of_epr_types:                   0
% 1.53/1.02  sat_num_of_non_cyclic_types:            0
% 1.53/1.02  sat_guarded_non_collapsed_types:        1
% 1.53/1.02  num_pure_diseq_elim:                    0
% 1.53/1.02  simp_replaced_by:                       0
% 1.53/1.02  res_preprocessed:                       111
% 1.53/1.02  prep_upred:                             0
% 1.53/1.02  prep_unflattend:                        29
% 1.53/1.02  smt_new_axioms:                         0
% 1.53/1.02  pred_elim_cands:                        3
% 1.53/1.02  pred_elim:                              3
% 1.53/1.02  pred_elim_cl:                           6
% 1.53/1.02  pred_elim_cycles:                       7
% 1.53/1.02  merged_defs:                            0
% 1.53/1.02  merged_defs_ncl:                        0
% 1.53/1.02  bin_hyper_res:                          0
% 1.53/1.02  prep_cycles:                            4
% 1.53/1.02  pred_elim_time:                         0.026
% 1.53/1.02  splitting_time:                         0.
% 1.53/1.02  sem_filter_time:                        0.
% 1.53/1.02  monotx_time:                            0.
% 1.53/1.02  subtype_inf_time:                       0.
% 1.53/1.02  
% 1.53/1.02  ------ Problem properties
% 1.53/1.02  
% 1.53/1.02  clauses:                                17
% 1.53/1.02  conjectures:                            6
% 1.53/1.02  epr:                                    5
% 1.53/1.02  horn:                                   11
% 1.53/1.02  ground:                                 13
% 1.53/1.02  unary:                                  0
% 1.53/1.02  binary:                                 8
% 1.53/1.02  lits:                                   48
% 1.53/1.02  lits_eq:                                22
% 1.53/1.02  fd_pure:                                0
% 1.53/1.02  fd_pseudo:                              0
% 1.53/1.02  fd_cond:                                0
% 1.53/1.02  fd_pseudo_cond:                         2
% 1.53/1.02  ac_symbols:                             0
% 1.53/1.02  
% 1.53/1.02  ------ Propositional Solver
% 1.53/1.02  
% 1.53/1.02  prop_solver_calls:                      29
% 1.53/1.02  prop_fast_solver_calls:                 1045
% 1.53/1.02  smt_solver_calls:                       0
% 1.53/1.02  smt_fast_solver_calls:                  0
% 1.53/1.02  prop_num_of_clauses:                    724
% 1.53/1.02  prop_preprocess_simplified:             2981
% 1.53/1.02  prop_fo_subsumed:                       25
% 1.53/1.02  prop_solver_time:                       0.
% 1.53/1.02  smt_solver_time:                        0.
% 1.53/1.02  smt_fast_solver_time:                   0.
% 1.53/1.02  prop_fast_solver_time:                  0.
% 1.53/1.02  prop_unsat_core_time:                   0.
% 1.53/1.02  
% 1.53/1.02  ------ QBF
% 1.53/1.02  
% 1.53/1.02  qbf_q_res:                              0
% 1.53/1.02  qbf_num_tautologies:                    0
% 1.53/1.02  qbf_prep_cycles:                        0
% 1.53/1.02  
% 1.53/1.02  ------ BMC1
% 1.53/1.02  
% 1.53/1.02  bmc1_current_bound:                     -1
% 1.53/1.02  bmc1_last_solved_bound:                 -1
% 1.53/1.02  bmc1_unsat_core_size:                   -1
% 1.53/1.02  bmc1_unsat_core_parents_size:           -1
% 1.53/1.02  bmc1_merge_next_fun:                    0
% 1.53/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.53/1.02  
% 1.53/1.02  ------ Instantiation
% 1.53/1.02  
% 1.53/1.02  inst_num_of_clauses:                    189
% 1.53/1.02  inst_num_in_passive:                    15
% 1.53/1.02  inst_num_in_active:                     159
% 1.53/1.02  inst_num_in_unprocessed:                15
% 1.53/1.02  inst_num_of_loops:                      210
% 1.53/1.02  inst_num_of_learning_restarts:          0
% 1.53/1.02  inst_num_moves_active_passive:          46
% 1.53/1.02  inst_lit_activity:                      0
% 1.53/1.02  inst_lit_activity_moves:                0
% 1.53/1.02  inst_num_tautologies:                   0
% 1.53/1.02  inst_num_prop_implied:                  0
% 1.53/1.02  inst_num_existing_simplified:           0
% 1.53/1.02  inst_num_eq_res_simplified:             0
% 1.53/1.02  inst_num_child_elim:                    0
% 1.53/1.02  inst_num_of_dismatching_blockings:      51
% 1.53/1.02  inst_num_of_non_proper_insts:           240
% 1.53/1.02  inst_num_of_duplicates:                 0
% 1.53/1.02  inst_inst_num_from_inst_to_res:         0
% 1.53/1.02  inst_dismatching_checking_time:         0.
% 1.53/1.02  
% 1.53/1.02  ------ Resolution
% 1.53/1.02  
% 1.53/1.02  res_num_of_clauses:                     0
% 1.53/1.02  res_num_in_passive:                     0
% 1.53/1.02  res_num_in_active:                      0
% 1.53/1.02  res_num_of_loops:                       115
% 1.53/1.02  res_forward_subset_subsumed:            43
% 1.53/1.02  res_backward_subset_subsumed:           0
% 1.53/1.02  res_forward_subsumed:                   0
% 1.53/1.02  res_backward_subsumed:                  0
% 1.53/1.02  res_forward_subsumption_resolution:     0
% 1.53/1.02  res_backward_subsumption_resolution:    0
% 1.53/1.02  res_clause_to_clause_subsumption:       76
% 1.53/1.02  res_orphan_elimination:                 0
% 1.53/1.02  res_tautology_del:                      48
% 1.53/1.02  res_num_eq_res_simplified:              1
% 1.53/1.02  res_num_sel_changes:                    0
% 1.53/1.02  res_moves_from_active_to_pass:          0
% 1.53/1.02  
% 1.53/1.02  ------ Superposition
% 1.53/1.02  
% 1.53/1.02  sup_time_total:                         0.
% 1.53/1.02  sup_time_generating:                    0.
% 1.53/1.02  sup_time_sim_full:                      0.
% 1.53/1.02  sup_time_sim_immed:                     0.
% 1.53/1.02  
% 1.53/1.02  sup_num_of_clauses:                     26
% 1.53/1.02  sup_num_in_active:                      17
% 1.53/1.02  sup_num_in_passive:                     9
% 1.53/1.02  sup_num_of_loops:                       40
% 1.53/1.02  sup_fw_superposition:                   16
% 1.53/1.02  sup_bw_superposition:                   21
% 1.53/1.02  sup_immediate_simplified:               11
% 1.53/1.02  sup_given_eliminated:                   0
% 1.53/1.02  comparisons_done:                       0
% 1.53/1.02  comparisons_avoided:                    12
% 1.53/1.02  
% 1.53/1.02  ------ Simplifications
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  sim_fw_subset_subsumed:                 5
% 1.53/1.02  sim_bw_subset_subsumed:                 7
% 1.53/1.02  sim_fw_subsumed:                        3
% 1.53/1.02  sim_bw_subsumed:                        0
% 1.53/1.02  sim_fw_subsumption_res:                 0
% 1.53/1.02  sim_bw_subsumption_res:                 0
% 1.53/1.02  sim_tautology_del:                      1
% 1.53/1.02  sim_eq_tautology_del:                   8
% 1.53/1.02  sim_eq_res_simp:                        3
% 1.53/1.02  sim_fw_demodulated:                     0
% 1.53/1.02  sim_bw_demodulated:                     19
% 1.53/1.02  sim_light_normalised:                   3
% 1.53/1.02  sim_joinable_taut:                      0
% 1.53/1.02  sim_joinable_simp:                      0
% 1.53/1.02  sim_ac_normalised:                      0
% 1.53/1.02  sim_smt_subsumption:                    0
% 1.53/1.02  
%------------------------------------------------------------------------------
