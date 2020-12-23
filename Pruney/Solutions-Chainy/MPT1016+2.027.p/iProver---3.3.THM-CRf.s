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
% DateTime   : Thu Dec  3 12:06:56 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  195 (35385 expanded)
%              Number of clauses        :  146 (11268 expanded)
%              Number of leaves         :   15 (6996 expanded)
%              Depth                    :   31
%              Number of atoms          :  755 (268649 expanded)
%              Number of equality atoms :  399 (91039 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f29,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f28,f27])).

fof(f51,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(flattening,[],[f10])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f32,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2172,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2512,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_283,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_579,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_283])).

cnf(c_580,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_1375,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_580])).

cnf(c_2158,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_1375])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_318,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_319,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_2168,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_2711,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_2168])).

cnf(c_2801,plain,
    ( k1_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2158,c_2711])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_445,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_2166,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_2178,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2166])).

cnf(c_2519,plain,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2178])).

cnf(c_3339,plain,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_2519])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_31,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_486,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_487,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_488,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_499,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_500,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_501,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2185,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2216,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2174,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2218,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2174])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2173,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2219,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_463,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_2165,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(X1_50,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0_50 = X1_50
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_2181,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2165])).

cnf(c_2235,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2181])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_512,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_513,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_2162,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_2239,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_525,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_526,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_2161,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_2240,plain,
    ( sK1(sK3) != sK0(sK3)
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_2184,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2700,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_267,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_268,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_2169,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_268])).

cnf(c_2695,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_2740,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2695])).

cnf(c_2741,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2740])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2175,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2767,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_2768,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2767])).

cnf(c_2188,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_2893,plain,
    ( sK5 != X0_50
    | sK4 != X0_50
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_2894,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_2524,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_3123,plain,
    ( v2_funct_1(sK3) = iProver_top
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_2239,c_2700,c_2741,c_2768])).

cnf(c_3124,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3123])).

cnf(c_2520,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2181])).

cnf(c_2899,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2520,c_2235,c_2700,c_2741,c_2768])).

cnf(c_3129,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | sP2_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_2899])).

cnf(c_2180,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(X1_50,k1_relat_1(sK3))
    | X0_50 = X1_50
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_2165])).

cnf(c_3152,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ sP2_iProver_split
    | k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,sK5)
    | sK5 = X0_50 ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_3153,plain,
    ( k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,sK5)
    | sK5 = X0_50
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3152])).

cnf(c_3155,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3153])).

cnf(c_2197,plain,
    ( ~ r2_hidden(X0_50,X0_48)
    | r2_hidden(X1_50,X1_48)
    | X1_50 != X0_50
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2880,plain,
    ( r2_hidden(X0_50,X0_48)
    | ~ r2_hidden(sK4,sK2)
    | X0_50 != sK4
    | X0_48 != sK2 ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_3164,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,sK2)
    | X0_50 != sK4
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2880])).

cnf(c_3165,plain,
    ( X0_50 != sK4
    | k1_relat_1(sK3) != sK2
    | r2_hidden(X0_50,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3164])).

cnf(c_3167,plain,
    ( sK4 != sK4
    | k1_relat_1(sK3) != sK2
    | r2_hidden(sK4,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3165])).

cnf(c_2163,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_2523,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2163])).

cnf(c_3100,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_501,c_2700,c_2741,c_2768])).

cnf(c_3101,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3100])).

cnf(c_3337,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_3101])).

cnf(c_2164,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_2522,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_2995,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2522,c_488,c_2700,c_2741,c_2768])).

cnf(c_2996,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2995])).

cnf(c_3338,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_2996])).

cnf(c_3498,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_2885,plain,
    ( r2_hidden(X0_50,X0_48)
    | ~ r2_hidden(sK5,sK2)
    | X0_50 != sK5
    | X0_48 != sK2 ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_3171,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | X0_50 != sK5
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2885])).

cnf(c_3717,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_3171])).

cnf(c_3718,plain,
    ( sK5 != sK5
    | k1_relat_1(sK3) != sK2
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3717])).

cnf(c_4274,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP2_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_4275,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4274])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2170,negated_conjecture,
    ( ~ r2_hidden(X0_50,sK2)
    | ~ r2_hidden(X1_50,sK2)
    | v2_funct_1(sK3)
    | X1_50 = X0_50
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4277,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_2170])).

cnf(c_4278,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4277])).

cnf(c_4288,plain,
    ( r2_hidden(X0_50,sK2) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3339,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,c_4278])).

cnf(c_4289,plain,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4288])).

cnf(c_4297,plain,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK5) = sK5
    | sK2 = k1_xboole_0
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_4289])).

cnf(c_4340,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,c_4278])).

cnf(c_4344,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4340,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,c_4278])).

cnf(c_4351,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4344,c_2711])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_363,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_604,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_363])).

cnf(c_605,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_2159,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_4355,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4344,c_2159])).

cnf(c_4371,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4355])).

cnf(c_4384,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4351,c_4371])).

cnf(c_5050,plain,
    ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4384,c_2996])).

cnf(c_5049,plain,
    ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4384,c_3101])).

cnf(c_2171,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2513,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_4357,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4344,c_2513])).

cnf(c_2186,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2792,plain,
    ( X0_48 != X1_48
    | X0_48 = sK2
    | sK2 != X1_48 ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_3488,plain,
    ( k1_relat_1(sK3) != X0_48
    | k1_relat_1(sK3) = sK2
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_3489,plain,
    ( k1_relat_1(sK3) = sK2
    | k1_relat_1(sK3) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3488])).

cnf(c_4420,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4357,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,c_3129,c_3155,c_3167,c_3337,c_3338,c_3489,c_3498,c_3718,c_4275,c_4278,c_4384])).

cnf(c_4429,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(superposition,[status(thm)],[c_3124,c_4420])).

cnf(c_2514,plain,
    ( X0_50 = X1_50
    | k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,X1_50)
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(X1_50,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_4353,plain,
    ( X0_50 = X1_50
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4344,c_2514])).

cnf(c_4536,plain,
    ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
    | X0_50 = X1_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4353,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,c_3129,c_3155,c_3167,c_3337,c_3338,c_3489,c_3498,c_3718,c_4275,c_4278,c_4384])).

cnf(c_4537,plain,
    ( X0_50 = X1_50
    | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4536])).

cnf(c_4631,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_50)
    | sK1(sK3) = X0_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4429,c_4537])).

cnf(c_4856,plain,
    ( sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4631])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5050,c_5049,c_4856,c_4420,c_2768,c_2741,c_2700,c_2240])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:51:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 2.18/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.00  
% 2.18/1.00  ------  iProver source info
% 2.18/1.00  
% 2.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.00  git: non_committed_changes: false
% 2.18/1.00  git: last_make_outside_of_git: false
% 2.18/1.00  
% 2.18/1.00  ------ 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options
% 2.18/1.00  
% 2.18/1.00  --out_options                           all
% 2.18/1.00  --tptp_safe_out                         true
% 2.18/1.00  --problem_path                          ""
% 2.18/1.00  --include_path                          ""
% 2.18/1.00  --clausifier                            res/vclausify_rel
% 2.18/1.00  --clausifier_options                    --mode clausify
% 2.18/1.00  --stdin                                 false
% 2.18/1.00  --stats_out                             all
% 2.18/1.00  
% 2.18/1.00  ------ General Options
% 2.18/1.00  
% 2.18/1.00  --fof                                   false
% 2.18/1.00  --time_out_real                         305.
% 2.18/1.00  --time_out_virtual                      -1.
% 2.18/1.00  --symbol_type_check                     false
% 2.18/1.00  --clausify_out                          false
% 2.18/1.00  --sig_cnt_out                           false
% 2.18/1.00  --trig_cnt_out                          false
% 2.18/1.00  --trig_cnt_out_tolerance                1.
% 2.18/1.00  --trig_cnt_out_sk_spl                   false
% 2.18/1.00  --abstr_cl_out                          false
% 2.18/1.00  
% 2.18/1.00  ------ Global Options
% 2.18/1.00  
% 2.18/1.00  --schedule                              default
% 2.18/1.00  --add_important_lit                     false
% 2.18/1.00  --prop_solver_per_cl                    1000
% 2.18/1.00  --min_unsat_core                        false
% 2.18/1.00  --soft_assumptions                      false
% 2.18/1.00  --soft_lemma_size                       3
% 2.18/1.00  --prop_impl_unit_size                   0
% 2.18/1.00  --prop_impl_unit                        []
% 2.18/1.00  --share_sel_clauses                     true
% 2.18/1.00  --reset_solvers                         false
% 2.18/1.00  --bc_imp_inh                            [conj_cone]
% 2.18/1.00  --conj_cone_tolerance                   3.
% 2.18/1.00  --extra_neg_conj                        none
% 2.18/1.00  --large_theory_mode                     true
% 2.18/1.00  --prolific_symb_bound                   200
% 2.18/1.00  --lt_threshold                          2000
% 2.18/1.00  --clause_weak_htbl                      true
% 2.18/1.00  --gc_record_bc_elim                     false
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing Options
% 2.18/1.00  
% 2.18/1.00  --preprocessing_flag                    true
% 2.18/1.00  --time_out_prep_mult                    0.1
% 2.18/1.00  --splitting_mode                        input
% 2.18/1.00  --splitting_grd                         true
% 2.18/1.00  --splitting_cvd                         false
% 2.18/1.00  --splitting_cvd_svl                     false
% 2.18/1.00  --splitting_nvd                         32
% 2.18/1.00  --sub_typing                            true
% 2.18/1.00  --prep_gs_sim                           true
% 2.18/1.00  --prep_unflatten                        true
% 2.18/1.00  --prep_res_sim                          true
% 2.18/1.00  --prep_upred                            true
% 2.18/1.00  --prep_sem_filter                       exhaustive
% 2.18/1.00  --prep_sem_filter_out                   false
% 2.18/1.00  --pred_elim                             true
% 2.18/1.00  --res_sim_input                         true
% 2.18/1.00  --eq_ax_congr_red                       true
% 2.18/1.00  --pure_diseq_elim                       true
% 2.18/1.00  --brand_transform                       false
% 2.18/1.00  --non_eq_to_eq                          false
% 2.18/1.00  --prep_def_merge                        true
% 2.18/1.00  --prep_def_merge_prop_impl              false
% 2.18/1.00  --prep_def_merge_mbd                    true
% 2.18/1.00  --prep_def_merge_tr_red                 false
% 2.18/1.00  --prep_def_merge_tr_cl                  false
% 2.18/1.00  --smt_preprocessing                     true
% 2.18/1.00  --smt_ac_axioms                         fast
% 2.18/1.00  --preprocessed_out                      false
% 2.18/1.00  --preprocessed_stats                    false
% 2.18/1.00  
% 2.18/1.00  ------ Abstraction refinement Options
% 2.18/1.00  
% 2.18/1.00  --abstr_ref                             []
% 2.18/1.00  --abstr_ref_prep                        false
% 2.18/1.00  --abstr_ref_until_sat                   false
% 2.18/1.00  --abstr_ref_sig_restrict                funpre
% 2.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.00  --abstr_ref_under                       []
% 2.18/1.00  
% 2.18/1.00  ------ SAT Options
% 2.18/1.00  
% 2.18/1.00  --sat_mode                              false
% 2.18/1.00  --sat_fm_restart_options                ""
% 2.18/1.00  --sat_gr_def                            false
% 2.18/1.00  --sat_epr_types                         true
% 2.18/1.00  --sat_non_cyclic_types                  false
% 2.18/1.00  --sat_finite_models                     false
% 2.18/1.00  --sat_fm_lemmas                         false
% 2.18/1.00  --sat_fm_prep                           false
% 2.18/1.00  --sat_fm_uc_incr                        true
% 2.18/1.00  --sat_out_model                         small
% 2.18/1.00  --sat_out_clauses                       false
% 2.18/1.00  
% 2.18/1.00  ------ QBF Options
% 2.18/1.00  
% 2.18/1.00  --qbf_mode                              false
% 2.18/1.00  --qbf_elim_univ                         false
% 2.18/1.00  --qbf_dom_inst                          none
% 2.18/1.00  --qbf_dom_pre_inst                      false
% 2.18/1.00  --qbf_sk_in                             false
% 2.18/1.00  --qbf_pred_elim                         true
% 2.18/1.00  --qbf_split                             512
% 2.18/1.00  
% 2.18/1.00  ------ BMC1 Options
% 2.18/1.00  
% 2.18/1.00  --bmc1_incremental                      false
% 2.18/1.00  --bmc1_axioms                           reachable_all
% 2.18/1.00  --bmc1_min_bound                        0
% 2.18/1.00  --bmc1_max_bound                        -1
% 2.18/1.00  --bmc1_max_bound_default                -1
% 2.18/1.00  --bmc1_symbol_reachability              true
% 2.18/1.00  --bmc1_property_lemmas                  false
% 2.18/1.00  --bmc1_k_induction                      false
% 2.18/1.00  --bmc1_non_equiv_states                 false
% 2.18/1.00  --bmc1_deadlock                         false
% 2.18/1.00  --bmc1_ucm                              false
% 2.18/1.00  --bmc1_add_unsat_core                   none
% 2.18/1.00  --bmc1_unsat_core_children              false
% 2.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.00  --bmc1_out_stat                         full
% 2.18/1.00  --bmc1_ground_init                      false
% 2.18/1.00  --bmc1_pre_inst_next_state              false
% 2.18/1.00  --bmc1_pre_inst_state                   false
% 2.18/1.00  --bmc1_pre_inst_reach_state             false
% 2.18/1.00  --bmc1_out_unsat_core                   false
% 2.18/1.00  --bmc1_aig_witness_out                  false
% 2.18/1.00  --bmc1_verbose                          false
% 2.18/1.00  --bmc1_dump_clauses_tptp                false
% 2.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.00  --bmc1_dump_file                        -
% 2.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.00  --bmc1_ucm_extend_mode                  1
% 2.18/1.00  --bmc1_ucm_init_mode                    2
% 2.18/1.00  --bmc1_ucm_cone_mode                    none
% 2.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.00  --bmc1_ucm_relax_model                  4
% 2.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.00  --bmc1_ucm_layered_model                none
% 2.18/1.00  --bmc1_ucm_max_lemma_size               10
% 2.18/1.00  
% 2.18/1.00  ------ AIG Options
% 2.18/1.00  
% 2.18/1.00  --aig_mode                              false
% 2.18/1.00  
% 2.18/1.00  ------ Instantiation Options
% 2.18/1.00  
% 2.18/1.00  --instantiation_flag                    true
% 2.18/1.00  --inst_sos_flag                         false
% 2.18/1.00  --inst_sos_phase                        true
% 2.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel_side                     num_symb
% 2.18/1.00  --inst_solver_per_active                1400
% 2.18/1.00  --inst_solver_calls_frac                1.
% 2.18/1.00  --inst_passive_queue_type               priority_queues
% 2.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.00  --inst_passive_queues_freq              [25;2]
% 2.18/1.00  --inst_dismatching                      true
% 2.18/1.00  --inst_eager_unprocessed_to_passive     true
% 2.18/1.00  --inst_prop_sim_given                   true
% 2.18/1.00  --inst_prop_sim_new                     false
% 2.18/1.00  --inst_subs_new                         false
% 2.18/1.00  --inst_eq_res_simp                      false
% 2.18/1.00  --inst_subs_given                       false
% 2.18/1.00  --inst_orphan_elimination               true
% 2.18/1.00  --inst_learning_loop_flag               true
% 2.18/1.00  --inst_learning_start                   3000
% 2.18/1.00  --inst_learning_factor                  2
% 2.18/1.00  --inst_start_prop_sim_after_learn       3
% 2.18/1.00  --inst_sel_renew                        solver
% 2.18/1.00  --inst_lit_activity_flag                true
% 2.18/1.00  --inst_restr_to_given                   false
% 2.18/1.00  --inst_activity_threshold               500
% 2.18/1.00  --inst_out_proof                        true
% 2.18/1.00  
% 2.18/1.00  ------ Resolution Options
% 2.18/1.00  
% 2.18/1.00  --resolution_flag                       true
% 2.18/1.00  --res_lit_sel                           adaptive
% 2.18/1.00  --res_lit_sel_side                      none
% 2.18/1.00  --res_ordering                          kbo
% 2.18/1.00  --res_to_prop_solver                    active
% 2.18/1.00  --res_prop_simpl_new                    false
% 2.18/1.00  --res_prop_simpl_given                  true
% 2.18/1.00  --res_passive_queue_type                priority_queues
% 2.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.00  --res_passive_queues_freq               [15;5]
% 2.18/1.00  --res_forward_subs                      full
% 2.18/1.00  --res_backward_subs                     full
% 2.18/1.00  --res_forward_subs_resolution           true
% 2.18/1.00  --res_backward_subs_resolution          true
% 2.18/1.00  --res_orphan_elimination                true
% 2.18/1.00  --res_time_limit                        2.
% 2.18/1.00  --res_out_proof                         true
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Options
% 2.18/1.00  
% 2.18/1.00  --superposition_flag                    true
% 2.18/1.00  --sup_passive_queue_type                priority_queues
% 2.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.00  --demod_completeness_check              fast
% 2.18/1.00  --demod_use_ground                      true
% 2.18/1.00  --sup_to_prop_solver                    passive
% 2.18/1.00  --sup_prop_simpl_new                    true
% 2.18/1.00  --sup_prop_simpl_given                  true
% 2.18/1.00  --sup_fun_splitting                     false
% 2.18/1.00  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  ------ Parsing...
% 2.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.01  ------ Proving...
% 2.18/1.01  ------ Problem Properties 
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  clauses                                 21
% 2.18/1.01  conjectures                             5
% 2.18/1.01  EPR                                     6
% 2.18/1.01  Horn                                    15
% 2.18/1.01  unary                                   1
% 2.18/1.01  binary                                  6
% 2.18/1.01  lits                                    60
% 2.18/1.01  lits eq                                 22
% 2.18/1.01  fd_pure                                 0
% 2.18/1.01  fd_pseudo                               0
% 2.18/1.01  fd_cond                                 0
% 2.18/1.01  fd_pseudo_cond                          2
% 2.18/1.01  AC symbols                              0
% 2.18/1.01  
% 2.18/1.01  ------ Schedule dynamic 5 is on 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  Current options:
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     none
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       false
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ Proving...
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS status Theorem for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  fof(f7,conjecture,(
% 2.18/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f8,negated_conjecture,(
% 2.18/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.18/1.01    inference(negated_conjecture,[],[f7])).
% 2.18/1.01  
% 2.18/1.01  fof(f17,plain,(
% 2.18/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.18/1.01    inference(ennf_transformation,[],[f8])).
% 2.18/1.01  
% 2.18/1.01  fof(f18,plain,(
% 2.18/1.01    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/1.01    inference(flattening,[],[f17])).
% 2.18/1.01  
% 2.18/1.01  fof(f24,plain,(
% 2.18/1.01    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/1.01    inference(nnf_transformation,[],[f18])).
% 2.18/1.01  
% 2.18/1.01  fof(f25,plain,(
% 2.18/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/1.01    inference(flattening,[],[f24])).
% 2.18/1.01  
% 2.18/1.01  fof(f26,plain,(
% 2.18/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/1.01    inference(rectify,[],[f25])).
% 2.18/1.01  
% 2.18/1.01  fof(f28,plain,(
% 2.18/1.01    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f27,plain,(
% 2.18/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f29,plain,(
% 2.18/1.01    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f28,f27])).
% 2.18/1.01  
% 2.18/1.01  fof(f51,plain,(
% 2.18/1.01    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f47,plain,(
% 2.18/1.01    v1_funct_2(sK3,sK2,sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f6,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f15,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f6])).
% 2.18/1.01  
% 2.18/1.01  fof(f16,plain,(
% 2.18/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(flattening,[],[f15])).
% 2.18/1.01  
% 2.18/1.01  fof(f23,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(nnf_transformation,[],[f16])).
% 2.18/1.01  
% 2.18/1.01  fof(f40,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f23])).
% 2.18/1.01  
% 2.18/1.01  fof(f48,plain,(
% 2.18/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f5,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f14,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f5])).
% 2.18/1.01  
% 2.18/1.01  fof(f39,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f14])).
% 2.18/1.01  
% 2.18/1.01  fof(f4,axiom,(
% 2.18/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f12,plain,(
% 2.18/1.01    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.18/1.01    inference(ennf_transformation,[],[f4])).
% 2.18/1.01  
% 2.18/1.01  fof(f13,plain,(
% 2.18/1.01    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(flattening,[],[f12])).
% 2.18/1.01  
% 2.18/1.01  fof(f38,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f13])).
% 2.18/1.01  
% 2.18/1.01  fof(f46,plain,(
% 2.18/1.01    v1_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f50,plain,(
% 2.18/1.01    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f3,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f10,plain,(
% 2.18/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f3])).
% 2.18/1.01  
% 2.18/1.01  fof(f11,plain,(
% 2.18/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f10])).
% 2.18/1.01  
% 2.18/1.01  fof(f19,plain,(
% 2.18/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(nnf_transformation,[],[f11])).
% 2.18/1.01  
% 2.18/1.01  fof(f20,plain,(
% 2.18/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(rectify,[],[f19])).
% 2.18/1.01  
% 2.18/1.01  fof(f21,plain,(
% 2.18/1.01    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f22,plain,(
% 2.18/1.01    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 2.18/1.01  
% 2.18/1.01  fof(f33,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f34,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f53,plain,(
% 2.18/1.01    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f52,plain,(
% 2.18/1.01    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f32,plain,(
% 2.18/1.01    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f35,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f36,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f1,axiom,(
% 2.18/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f9,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(ennf_transformation,[],[f1])).
% 2.18/1.01  
% 2.18/1.01  fof(f30,plain,(
% 2.18/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f9])).
% 2.18/1.01  
% 2.18/1.01  fof(f2,axiom,(
% 2.18/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f31,plain,(
% 2.18/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f2])).
% 2.18/1.01  
% 2.18/1.01  fof(f49,plain,(
% 2.18/1.01    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f41,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f23])).
% 2.18/1.01  
% 2.18/1.01  fof(f58,plain,(
% 2.18/1.01    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.18/1.01    inference(equality_resolution,[],[f41])).
% 2.18/1.01  
% 2.18/1.01  cnf(c_18,negated_conjecture,
% 2.18/1.01      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2172,negated_conjecture,
% 2.18/1.01      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2512,plain,
% 2.18/1.01      ( r2_hidden(sK5,sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_22,negated_conjecture,
% 2.18/1.01      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_15,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_21,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_282,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK3 != X0
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_283,plain,
% 2.18/1.01      ( ~ v1_funct_2(sK3,X0,X1)
% 2.18/1.01      | k1_relset_1(X0,X1,sK3) = X0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | k1_xboole_0 = X1 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_282]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_579,plain,
% 2.18/1.01      ( k1_relset_1(X0,X1,sK3) = X0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK2 != X0
% 2.18/1.01      | sK2 != X1
% 2.18/1.01      | sK3 != sK3
% 2.18/1.01      | k1_xboole_0 = X1 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_283]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_580,plain,
% 2.18/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | k1_xboole_0 = sK2 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_579]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1375,plain,
% 2.18/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 2.18/1.01      inference(equality_resolution_simp,[status(thm)],[c_580]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2158,plain,
% 2.18/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_1375]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_9,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_318,plain,
% 2.18/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK3 != X2 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_319,plain,
% 2.18/1.01      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_318]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2168,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_319]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2711,plain,
% 2.18/1.01      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_2168]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2801,plain,
% 2.18/1.01      ( k1_relat_1(sK3) = sK2 | sK2 = k1_xboole_0 ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2158,c_2711]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_7,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.18/1.01      | ~ v1_funct_1(X1)
% 2.18/1.01      | ~ v2_funct_1(X1)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_23,negated_conjecture,
% 2.18/1.01      ( v1_funct_1(sK3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_444,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.18/1.01      | ~ v2_funct_1(X1)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
% 2.18/1.01      | sK3 != X1 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_445,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.18/1.01      | ~ v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0) = X0 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_444]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2166,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_445]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2178,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
% 2.18/1.01      | ~ sP1_iProver_split ),
% 2.18/1.01      inference(splitting,
% 2.18/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.18/1.01                [c_2166]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2519,plain,
% 2.18/1.01      ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
% 2.18/1.01      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | sP1_iProver_split != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2178]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3339,plain,
% 2.18/1.01      ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
% 2.18/1.01      | sK2 = k1_xboole_0
% 2.18/1.01      | r2_hidden(X0_50,sK2) != iProver_top
% 2.18/1.01      | sP1_iProver_split != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2801,c_2519]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_19,negated_conjecture,
% 2.18/1.01      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_30,plain,
% 2.18/1.01      ( r2_hidden(sK4,sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_31,plain,
% 2.18/1.01      ( r2_hidden(sK5,sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5,plain,
% 2.18/1.01      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_486,plain,
% 2.18/1.01      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_487,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_486]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_488,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4,plain,
% 2.18/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_499,plain,
% 2.18/1.01      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_500,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_499]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_501,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2185,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2216,plain,
% 2.18/1.01      ( sK4 = sK4 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2185]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_16,negated_conjecture,
% 2.18/1.01      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.18/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2174,negated_conjecture,
% 2.18/1.01      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2218,plain,
% 2.18/1.01      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2174]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_17,negated_conjecture,
% 2.18/1.01      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.18/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2173,negated_conjecture,
% 2.18/1.01      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2219,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.18/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.18/1.01      | ~ v1_funct_1(X1)
% 2.18/1.01      | ~ v2_funct_1(X1)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | X0 = X2
% 2.18/1.01      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_462,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.18/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.18/1.01      | ~ v2_funct_1(X1)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | X0 = X2
% 2.18/1.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.18/1.01      | sK3 != X1 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_463,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.18/1.01      | ~ v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | X0 = X1
% 2.18/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_462]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2165,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(X1_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | X0_50 = X1_50
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_463]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2181,plain,
% 2.18/1.01      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP2_iProver_split ),
% 2.18/1.01      inference(splitting,
% 2.18/1.01                [splitting(split),new_symbols(definition,[])],
% 2.18/1.01                [c_2165]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2235,plain,
% 2.18/1.01      ( v2_funct_1(sK3) != iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top
% 2.18/1.01      | sP2_iProver_split = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2181]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3,plain,
% 2.18/1.01      ( ~ v1_funct_1(X0)
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_512,plain,
% 2.18/1.01      ( v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_513,plain,
% 2.18/1.01      ( v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_512]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2162,plain,
% 2.18/1.01      ( v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3)
% 2.18/1.01      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_513]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2239,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2,plain,
% 2.18/1.01      ( ~ v1_funct_1(X0)
% 2.18/1.01      | v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | sK1(X0) != sK0(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_525,plain,
% 2.18/1.01      ( v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | sK1(X0) != sK0(X0)
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_526,plain,
% 2.18/1.01      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_525]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2161,plain,
% 2.18/1.01      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_526]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2240,plain,
% 2.18/1.01      ( sK1(sK3) != sK0(sK3)
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2184,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2700,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2184]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_0,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_267,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0)
% 2.18/1.01      | v1_relat_1(X1)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0)
% 2.18/1.01      | sK3 != X1 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_268,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0)
% 2.18/1.01      | v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_267]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2169,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0_48)
% 2.18/1.01      | v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0_48) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_268]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2695,plain,
% 2.18/1.01      ( ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48))
% 2.18/1.01      | v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2169]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2740,plain,
% 2.18/1.01      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2695]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2741,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2740]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1,plain,
% 2.18/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2175,plain,
% 2.18/1.01      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2767,plain,
% 2.18/1.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2175]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2768,plain,
% 2.18/1.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2767]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2188,plain,
% 2.18/1.01      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2893,plain,
% 2.18/1.01      ( sK5 != X0_50 | sK4 != X0_50 | sK4 = sK5 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2188]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2894,plain,
% 2.18/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2893]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2524,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3123,plain,
% 2.18/1.01      ( v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2524,c_2239,c_2700,c_2741,c_2768]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3124,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_3123]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2520,plain,
% 2.18/1.01      ( v2_funct_1(sK3) != iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top
% 2.18/1.01      | sP2_iProver_split = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2181]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2899,plain,
% 2.18/1.01      ( v2_funct_1(sK3) != iProver_top
% 2.18/1.01      | sP2_iProver_split = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2520,c_2235,c_2700,c_2741,c_2768]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3129,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.18/1.01      | sP2_iProver_split = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_3124,c_2899]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2180,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(X1_50,k1_relat_1(sK3))
% 2.18/1.01      | X0_50 = X1_50
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
% 2.18/1.01      | ~ sP2_iProver_split ),
% 2.18/1.01      inference(splitting,
% 2.18/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.18/1.01                [c_2165]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3152,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.18/1.01      | ~ sP2_iProver_split
% 2.18/1.01      | k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,sK5)
% 2.18/1.01      | sK5 = X0_50 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2180]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3153,plain,
% 2.18/1.01      ( k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,sK5)
% 2.18/1.01      | sK5 = X0_50
% 2.18/1.01      | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | sP2_iProver_split != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3152]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3155,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
% 2.18/1.01      | sK5 = sK4
% 2.18/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | sP2_iProver_split != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3153]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2197,plain,
% 2.18/1.01      ( ~ r2_hidden(X0_50,X0_48)
% 2.18/1.01      | r2_hidden(X1_50,X1_48)
% 2.18/1.01      | X1_50 != X0_50
% 2.18/1.01      | X1_48 != X0_48 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2880,plain,
% 2.18/1.01      ( r2_hidden(X0_50,X0_48)
% 2.18/1.01      | ~ r2_hidden(sK4,sK2)
% 2.18/1.01      | X0_50 != sK4
% 2.18/1.01      | X0_48 != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2197]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3164,plain,
% 2.18/1.01      ( r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(sK4,sK2)
% 2.18/1.01      | X0_50 != sK4
% 2.18/1.01      | k1_relat_1(sK3) != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2880]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3165,plain,
% 2.18/1.01      ( X0_50 != sK4
% 2.18/1.01      | k1_relat_1(sK3) != sK2
% 2.18/1.01      | r2_hidden(X0_50,k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | r2_hidden(sK4,sK2) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3164]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3167,plain,
% 2.18/1.01      ( sK4 != sK4
% 2.18/1.01      | k1_relat_1(sK3) != sK2
% 2.18/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | r2_hidden(sK4,sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3165]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2163,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_500]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2523,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2163]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3100,plain,
% 2.18/1.01      ( v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2523,c_501,c_2700,c_2741,c_2768]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3101,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_3100]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3337,plain,
% 2.18/1.01      ( sK2 = k1_xboole_0
% 2.18/1.01      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2801,c_3101]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2164,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | ~ v1_relat_1(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_487]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2522,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2995,plain,
% 2.18/1.01      ( v2_funct_1(sK3) = iProver_top
% 2.18/1.01      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2522,c_488,c_2700,c_2741,c_2768]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2996,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_2995]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3338,plain,
% 2.18/1.01      ( sK2 = k1_xboole_0
% 2.18/1.01      | r2_hidden(sK0(sK3),sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2801,c_2996]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3498,plain,
% 2.18/1.01      ( sK5 = sK5 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2185]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2885,plain,
% 2.18/1.01      ( r2_hidden(X0_50,X0_48)
% 2.18/1.01      | ~ r2_hidden(sK5,sK2)
% 2.18/1.01      | X0_50 != sK5
% 2.18/1.01      | X0_48 != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2197]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3171,plain,
% 2.18/1.01      ( r2_hidden(X0_50,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(sK5,sK2)
% 2.18/1.01      | X0_50 != sK5
% 2.18/1.01      | k1_relat_1(sK3) != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2885]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3717,plain,
% 2.18/1.01      ( r2_hidden(sK5,k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(sK5,sK2)
% 2.18/1.01      | sK5 != sK5
% 2.18/1.01      | k1_relat_1(sK3) != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3171]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3718,plain,
% 2.18/1.01      ( sK5 != sK5
% 2.18/1.01      | k1_relat_1(sK3) != sK2
% 2.18/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.18/1.01      | r2_hidden(sK5,sK2) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3717]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4274,plain,
% 2.18/1.01      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.18/1.01      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.18/1.01      | ~ sP2_iProver_split
% 2.18/1.01      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.18/1.01      | sK1(sK3) = sK0(sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2180]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4275,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.18/1.01      | sK1(sK3) = sK0(sK3)
% 2.18/1.01      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.18/1.01      | sP2_iProver_split != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_4274]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_20,negated_conjecture,
% 2.18/1.01      ( ~ r2_hidden(X0,sK2)
% 2.18/1.01      | ~ r2_hidden(X1,sK2)
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | X1 = X0
% 2.18/1.01      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2170,negated_conjecture,
% 2.18/1.01      ( ~ r2_hidden(X0_50,sK2)
% 2.18/1.01      | ~ r2_hidden(X1_50,sK2)
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | X1_50 = X0_50
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4277,plain,
% 2.18/1.01      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.18/1.01      | ~ r2_hidden(sK0(sK3),sK2)
% 2.18/1.01      | v2_funct_1(sK3)
% 2.18/1.01      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.18/1.01      | sK1(sK3) = sK0(sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2170]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4278,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.18/1.01      | sK1(sK3) = sK0(sK3)
% 2.18/1.01      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.18/1.01      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_4277]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4288,plain,
% 2.18/1.01      ( r2_hidden(X0_50,sK2) != iProver_top
% 2.18/1.01      | sK2 = k1_xboole_0
% 2.18/1.01      | k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3339,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,
% 2.18/1.01                 c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,
% 2.18/1.01                 c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,
% 2.18/1.01                 c_4278]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4289,plain,
% 2.18/1.01      ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_50) = X0_50
% 2.18/1.01      | sK2 = k1_xboole_0
% 2.18/1.01      | r2_hidden(X0_50,sK2) != iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_4288]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4297,plain,
% 2.18/1.01      ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK5) = sK5
% 2.18/1.01      | sK2 = k1_xboole_0
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2512,c_4289]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4340,plain,
% 2.18/1.01      ( sK2 = k1_xboole_0 | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4297,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,
% 2.18/1.01                 c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,
% 2.18/1.01                 c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,
% 2.18/1.01                 c_4278]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4344,plain,
% 2.18/1.01      ( sK2 = k1_xboole_0 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4340,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,
% 2.18/1.01                 c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,
% 2.18/1.01                 c_3129,c_3155,c_3167,c_3337,c_3338,c_3498,c_3718,c_4275,
% 2.18/1.01                 c_4278]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4351,plain,
% 2.18/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4344,c_2711]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_14,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.18/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_362,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.18/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_363,plain,
% 2.18/1.01      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 2.18/1.01      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_362]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_604,plain,
% 2.18/1.01      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK2 != X0
% 2.18/1.01      | sK2 != k1_xboole_0
% 2.18/1.01      | sK3 != sK3 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_363]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_605,plain,
% 2.18/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | sK2 != k1_xboole_0 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_604]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2159,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 2.18/1.01      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.18/1.01      | sK2 != k1_xboole_0 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_605]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4355,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.18/1.01      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.18/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4344,c_2159]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4371,plain,
% 2.18/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 2.18/1.01      inference(equality_resolution_simp,[status(thm)],[c_4355]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4384,plain,
% 2.18/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_4351,c_4371]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5050,plain,
% 2.18/1.01      ( r2_hidden(sK0(sK3),k1_xboole_0) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4384,c_2996]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5049,plain,
% 2.18/1.01      ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4384,c_3101]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2171,negated_conjecture,
% 2.18/1.01      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2513,plain,
% 2.18/1.01      ( r2_hidden(sK4,sK2) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4357,plain,
% 2.18/1.01      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 2.18/1.01      | v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4344,c_2513]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2186,plain,
% 2.18/1.01      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2792,plain,
% 2.18/1.01      ( X0_48 != X1_48 | X0_48 = sK2 | sK2 != X1_48 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2186]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3488,plain,
% 2.18/1.01      ( k1_relat_1(sK3) != X0_48 | k1_relat_1(sK3) = sK2 | sK2 != X0_48 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2792]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3489,plain,
% 2.18/1.01      ( k1_relat_1(sK3) = sK2
% 2.18/1.01      | k1_relat_1(sK3) != k1_xboole_0
% 2.18/1.01      | sK2 != k1_xboole_0 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3488]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4420,plain,
% 2.18/1.01      ( v2_funct_1(sK3) != iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4357,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,
% 2.18/1.01                 c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,
% 2.18/1.01                 c_3129,c_3155,c_3167,c_3337,c_3338,c_3489,c_3498,c_3718,
% 2.18/1.01                 c_4275,c_4278,c_4384]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4429,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_3124,c_4420]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2514,plain,
% 2.18/1.01      ( X0_50 = X1_50
% 2.18/1.01      | k1_funct_1(sK3,X0_50) != k1_funct_1(sK3,X1_50)
% 2.18/1.01      | r2_hidden(X0_50,sK2) != iProver_top
% 2.18/1.01      | r2_hidden(X1_50,sK2) != iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4353,plain,
% 2.18/1.01      ( X0_50 = X1_50
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
% 2.18/1.01      | r2_hidden(X1_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4344,c_2514]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4536,plain,
% 2.18/1.01      ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | r2_hidden(X1_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
% 2.18/1.01      | X0_50 = X1_50 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4353,c_30,c_31,c_488,c_501,c_2216,c_2218,c_2219,
% 2.18/1.01                 c_2235,c_2239,c_2240,c_2700,c_2741,c_2768,c_2801,c_2894,
% 2.18/1.01                 c_3129,c_3155,c_3167,c_3337,c_3338,c_3489,c_3498,c_3718,
% 2.18/1.01                 c_4275,c_4278,c_4384]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4537,plain,
% 2.18/1.01      ( X0_50 = X1_50
% 2.18/1.01      | k1_funct_1(sK3,X1_50) != k1_funct_1(sK3,X0_50)
% 2.18/1.01      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | r2_hidden(X1_50,k1_xboole_0) != iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_4536]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4631,plain,
% 2.18/1.01      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_50)
% 2.18/1.01      | sK1(sK3) = X0_50
% 2.18/1.01      | r2_hidden(X0_50,k1_xboole_0) != iProver_top
% 2.18/1.01      | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_4429,c_4537]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4856,plain,
% 2.18/1.01      ( sK1(sK3) = sK0(sK3)
% 2.18/1.01      | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
% 2.18/1.01      | r2_hidden(sK0(sK3),k1_xboole_0) != iProver_top ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_4631]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(contradiction,plain,
% 2.18/1.01      ( $false ),
% 2.18/1.01      inference(minisat,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_5050,c_5049,c_4856,c_4420,c_2768,c_2741,c_2700,c_2240]) ).
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  ------                               Statistics
% 2.18/1.01  
% 2.18/1.01  ------ General
% 2.18/1.01  
% 2.18/1.01  abstr_ref_over_cycles:                  0
% 2.18/1.01  abstr_ref_under_cycles:                 0
% 2.18/1.01  gc_basic_clause_elim:                   0
% 2.18/1.01  forced_gc_time:                         0
% 2.18/1.01  parsing_time:                           0.012
% 2.18/1.01  unif_index_cands_time:                  0.
% 2.18/1.01  unif_index_add_time:                    0.
% 2.18/1.01  orderings_time:                         0.
% 2.18/1.01  out_proof_time:                         0.012
% 2.18/1.01  total_time:                             0.152
% 2.18/1.01  num_of_symbols:                         57
% 2.18/1.01  num_of_terms:                           1884
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing
% 2.18/1.01  
% 2.18/1.01  num_of_splits:                          3
% 2.18/1.01  num_of_split_atoms:                     3
% 2.18/1.01  num_of_reused_defs:                     0
% 2.18/1.01  num_eq_ax_congr_red:                    7
% 2.18/1.01  num_of_sem_filtered_clauses:            1
% 2.18/1.01  num_of_subtypes:                        3
% 2.18/1.01  monotx_restored_types:                  0
% 2.18/1.01  sat_num_of_epr_types:                   0
% 2.18/1.01  sat_num_of_non_cyclic_types:            0
% 2.18/1.01  sat_guarded_non_collapsed_types:        1
% 2.18/1.01  num_pure_diseq_elim:                    0
% 2.18/1.01  simp_replaced_by:                       0
% 2.18/1.01  res_preprocessed:                       121
% 2.18/1.01  prep_upred:                             0
% 2.18/1.01  prep_unflattend:                        31
% 2.18/1.01  smt_new_axioms:                         0
% 2.18/1.01  pred_elim_cands:                        3
% 2.18/1.01  pred_elim:                              3
% 2.18/1.01  pred_elim_cl:                           6
% 2.18/1.01  pred_elim_cycles:                       5
% 2.18/1.01  merged_defs:                            0
% 2.18/1.01  merged_defs_ncl:                        0
% 2.18/1.01  bin_hyper_res:                          0
% 2.18/1.01  prep_cycles:                            4
% 2.18/1.01  pred_elim_time:                         0.027
% 2.18/1.01  splitting_time:                         0.
% 2.18/1.01  sem_filter_time:                        0.
% 2.18/1.01  monotx_time:                            0.
% 2.18/1.01  subtype_inf_time:                       0.
% 2.18/1.01  
% 2.18/1.01  ------ Problem properties
% 2.18/1.01  
% 2.18/1.01  clauses:                                21
% 2.18/1.01  conjectures:                            5
% 2.18/1.01  epr:                                    6
% 2.18/1.01  horn:                                   15
% 2.18/1.01  ground:                                 14
% 2.18/1.01  unary:                                  1
% 2.18/1.01  binary:                                 6
% 2.18/1.01  lits:                                   60
% 2.18/1.01  lits_eq:                                22
% 2.18/1.01  fd_pure:                                0
% 2.18/1.01  fd_pseudo:                              0
% 2.18/1.01  fd_cond:                                0
% 2.18/1.01  fd_pseudo_cond:                         2
% 2.18/1.01  ac_symbols:                             0
% 2.18/1.01  
% 2.18/1.01  ------ Propositional Solver
% 2.18/1.01  
% 2.18/1.01  prop_solver_calls:                      30
% 2.18/1.01  prop_fast_solver_calls:                 1294
% 2.18/1.01  smt_solver_calls:                       0
% 2.18/1.01  smt_fast_solver_calls:                  0
% 2.18/1.01  prop_num_of_clauses:                    864
% 2.18/1.01  prop_preprocess_simplified:             3507
% 2.18/1.01  prop_fo_subsumed:                       36
% 2.18/1.01  prop_solver_time:                       0.
% 2.18/1.01  smt_solver_time:                        0.
% 2.18/1.01  smt_fast_solver_time:                   0.
% 2.18/1.01  prop_fast_solver_time:                  0.
% 2.18/1.01  prop_unsat_core_time:                   0.
% 2.18/1.01  
% 2.18/1.01  ------ QBF
% 2.18/1.01  
% 2.18/1.01  qbf_q_res:                              0
% 2.18/1.01  qbf_num_tautologies:                    0
% 2.18/1.01  qbf_prep_cycles:                        0
% 2.18/1.01  
% 2.18/1.01  ------ BMC1
% 2.18/1.01  
% 2.18/1.01  bmc1_current_bound:                     -1
% 2.18/1.01  bmc1_last_solved_bound:                 -1
% 2.18/1.01  bmc1_unsat_core_size:                   -1
% 2.18/1.01  bmc1_unsat_core_parents_size:           -1
% 2.18/1.01  bmc1_merge_next_fun:                    0
% 2.18/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation
% 2.18/1.01  
% 2.18/1.01  inst_num_of_clauses:                    265
% 2.18/1.01  inst_num_in_passive:                    3
% 2.18/1.01  inst_num_in_active:                     204
% 2.18/1.01  inst_num_in_unprocessed:                58
% 2.18/1.01  inst_num_of_loops:                      310
% 2.18/1.01  inst_num_of_learning_restarts:          0
% 2.18/1.01  inst_num_moves_active_passive:          100
% 2.18/1.01  inst_lit_activity:                      0
% 2.18/1.01  inst_lit_activity_moves:                0
% 2.18/1.01  inst_num_tautologies:                   0
% 2.18/1.01  inst_num_prop_implied:                  0
% 2.18/1.01  inst_num_existing_simplified:           0
% 2.18/1.01  inst_num_eq_res_simplified:             0
% 2.18/1.01  inst_num_child_elim:                    0
% 2.18/1.01  inst_num_of_dismatching_blockings:      293
% 2.18/1.01  inst_num_of_non_proper_insts:           586
% 2.18/1.01  inst_num_of_duplicates:                 0
% 2.18/1.01  inst_inst_num_from_inst_to_res:         0
% 2.18/1.01  inst_dismatching_checking_time:         0.
% 2.18/1.01  
% 2.18/1.01  ------ Resolution
% 2.18/1.01  
% 2.18/1.01  res_num_of_clauses:                     0
% 2.18/1.01  res_num_in_passive:                     0
% 2.18/1.01  res_num_in_active:                      0
% 2.18/1.01  res_num_of_loops:                       125
% 2.18/1.01  res_forward_subset_subsumed:            115
% 2.18/1.01  res_backward_subset_subsumed:           0
% 2.18/1.01  res_forward_subsumed:                   0
% 2.18/1.01  res_backward_subsumed:                  0
% 2.18/1.01  res_forward_subsumption_resolution:     0
% 2.18/1.01  res_backward_subsumption_resolution:    0
% 2.18/1.01  res_clause_to_clause_subsumption:       97
% 2.18/1.01  res_orphan_elimination:                 0
% 2.18/1.01  res_tautology_del:                      133
% 2.18/1.01  res_num_eq_res_simplified:              1
% 2.18/1.01  res_num_sel_changes:                    0
% 2.18/1.01  res_moves_from_active_to_pass:          0
% 2.18/1.01  
% 2.18/1.01  ------ Superposition
% 2.18/1.01  
% 2.18/1.01  sup_time_total:                         0.
% 2.18/1.01  sup_time_generating:                    0.
% 2.18/1.01  sup_time_sim_full:                      0.
% 2.18/1.01  sup_time_sim_immed:                     0.
% 2.18/1.01  
% 2.18/1.01  sup_num_of_clauses:                     40
% 2.18/1.01  sup_num_in_active:                      27
% 2.18/1.01  sup_num_in_passive:                     13
% 2.18/1.01  sup_num_of_loops:                       60
% 2.18/1.01  sup_fw_superposition:                   25
% 2.18/1.01  sup_bw_superposition:                   39
% 2.18/1.01  sup_immediate_simplified:               15
% 2.18/1.01  sup_given_eliminated:                   0
% 2.18/1.01  comparisons_done:                       0
% 2.18/1.01  comparisons_avoided:                    21
% 2.18/1.01  
% 2.18/1.01  ------ Simplifications
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  sim_fw_subset_subsumed:                 13
% 2.18/1.01  sim_bw_subset_subsumed:                 11
% 2.18/1.01  sim_fw_subsumed:                        0
% 2.18/1.01  sim_bw_subsumed:                        0
% 2.18/1.01  sim_fw_subsumption_res:                 0
% 2.18/1.01  sim_bw_subsumption_res:                 0
% 2.18/1.01  sim_tautology_del:                      5
% 2.18/1.01  sim_eq_tautology_del:                   11
% 2.18/1.01  sim_eq_res_simp:                        1
% 2.18/1.01  sim_fw_demodulated:                     0
% 2.18/1.01  sim_bw_demodulated:                     23
% 2.18/1.01  sim_light_normalised:                   2
% 2.18/1.01  sim_joinable_taut:                      0
% 2.18/1.01  sim_joinable_simp:                      0
% 2.18/1.01  sim_ac_normalised:                      0
% 2.18/1.01  sim_smt_subsumption:                    0
% 2.18/1.01  
%------------------------------------------------------------------------------
