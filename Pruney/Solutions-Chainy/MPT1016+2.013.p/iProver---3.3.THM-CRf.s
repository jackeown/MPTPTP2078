%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:53 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  191 (78966 expanded)
%              Number of clauses        :  148 (23234 expanded)
%              Number of leaves         :   13 (15730 expanded)
%              Depth                    :   34
%              Number of atoms          :  740 (612219 expanded)
%              Number of equality atoms :  429 (210456 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f24,f23])).

fof(f40,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
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

fof(f43,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
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

fof(f42,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
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
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_235,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_236,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_594,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_236])).

cnf(c_595,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_1156,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_595])).

cnf(c_1796,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_1156])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_271,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_272,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1805,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_2224,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1805])).

cnf(c_2290,plain,
    ( k1_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1796,c_2224])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_416,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_417,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1801,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_2077,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_1860,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_1815,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_2206,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_280,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_281,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_1804,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_2208,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2209,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2532,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2077,c_1860,c_2206,c_2209])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1809,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2070,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_2539,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2532,c_2070])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1799,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
    | ~ r2_hidden(X1_49,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49 ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_1811,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
    | ~ r2_hidden(X1_49,k1_relat_1(sK3))
    | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1799])).

cnf(c_2080,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_2553,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_2080])).

cnf(c_2747,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2553])).

cnf(c_2814,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | sK2 = k1_xboole_0
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_2747])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_403,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_404,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1802,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_2076,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_405,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_2488,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2076,c_405,c_2206,c_2209])).

cnf(c_2663,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_2488])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_429,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_430,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1800,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(subtyping,[status(esa)],[c_430])).

cnf(c_1861,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1806,negated_conjecture,
    ( ~ r2_hidden(X0_49,sK2)
    | ~ r2_hidden(X1_49,sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,X1_49) != k1_funct_1(sK3,X0_49)
    | X1_49 = X0_49 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2235,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2236,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2235])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_390,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_391,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1803,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_2075,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_392,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_2481,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2075,c_392,c_2206,c_2209])).

cnf(c_2664,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_2481])).

cnf(c_2853,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2663,c_1860,c_1861,c_2206,c_2209,c_2236,c_2664])).

cnf(c_2860,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2853,c_2070])).

cnf(c_2874,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
    | sK5 = X0_49
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2080])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1829,plain,
    ( ~ r2_hidden(X0_49,X0_46)
    | r2_hidden(X1_49,X1_46)
    | X1_49 != X0_49
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2595,plain,
    ( r2_hidden(X0_49,X0_46)
    | ~ r2_hidden(sK5,sK2)
    | X0_49 != sK5
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_2793,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_2794,plain,
    ( sK5 != sK5
    | k1_relat_1(sK3) != sK2
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2793])).

cnf(c_1812,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1799])).

cnf(c_2079,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_1862,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_2393,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_1862,c_2206,c_2209])).

cnf(c_2859,plain,
    ( sK2 = k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_2393])).

cnf(c_1817,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2990,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_3053,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
    | sK5 = X0_49
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2874,c_28,c_1860,c_1861,c_2206,c_2209,c_2236,c_2290,c_2663,c_2664,c_2794,c_2859,c_2990])).

cnf(c_3065,plain,
    ( sK5 = sK4
    | sK2 = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3053])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1810,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1849,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_1850,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_2608,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_2609,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK4 = sK5
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2608])).

cnf(c_3126,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3065,c_28,c_1849,c_1850,c_1860,c_1861,c_2206,c_2209,c_2236,c_2290,c_2609,c_2663,c_2664,c_2794,c_2859,c_2990])).

cnf(c_3132,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_3126])).

cnf(c_3135,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_27,c_2853,c_3132])).

cnf(c_3142,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3135,c_2224])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_327,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_328,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_619,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_328])).

cnf(c_620,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_1797,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_3146,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3135,c_1797])).

cnf(c_3162,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3146])).

cnf(c_3175,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3142,c_3162])).

cnf(c_3444,plain,
    ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3175,c_2488])).

cnf(c_2073,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,sK2) != iProver_top
    | r2_hidden(X1_49,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1806])).

cnf(c_2554,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0_49
    | r2_hidden(X0_49,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_2073])).

cnf(c_3141,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3135,c_2554])).

cnf(c_2281,plain,
    ( sK1(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2314,plain,
    ( sK0(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2649,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2554])).

cnf(c_2732,plain,
    ( r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_1860,c_1861,c_2206,c_2209,c_2236])).

cnf(c_1819,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2264,plain,
    ( X0_46 != X1_46
    | sK2 != X1_46
    | sK2 = X0_46 ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2910,plain,
    ( k1_relat_1(sK3) != X0_46
    | sK2 != X0_46
    | sK2 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_2912,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_relat_1(sK3)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_2257,plain,
    ( r2_hidden(X0_49,X0_46)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | X0_49 != sK0(sK3)
    | X0_46 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_2313,plain,
    ( r2_hidden(sK0(sK3),X0_46)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | sK0(sK3) != sK0(sK3)
    | X0_46 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_2911,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | r2_hidden(sK0(sK3),sK2)
    | sK0(sK3) != sK0(sK3)
    | sK2 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_2913,plain,
    ( sK0(sK3) != sK0(sK3)
    | sK2 != k1_relat_1(sK3)
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_2954,plain,
    ( ~ r2_hidden(X0_49,X0_46)
    | r2_hidden(sK1(sK3),sK2)
    | sK1(sK3) != X0_49
    | sK2 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_3105,plain,
    ( ~ r2_hidden(sK1(sK3),X0_46)
    | r2_hidden(sK1(sK3),sK2)
    | sK1(sK3) != sK1(sK3)
    | sK2 != X0_46 ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(c_3106,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK2 != X0_46
    | r2_hidden(sK1(sK3),X0_46) != iProver_top
    | r2_hidden(sK1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3105])).

cnf(c_3108,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK2 != k1_xboole_0
    | r2_hidden(sK1(sK3),sK2) = iProver_top
    | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3106])).

cnf(c_3323,plain,
    ( r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_27,c_392,c_2206,c_2209,c_2281,c_2314,c_2732,c_2853,c_2912,c_2913,c_3108,c_3132,c_3175])).

cnf(c_3512,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_3323])).

cnf(c_3518,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3512,c_2070])).

cnf(c_3446,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3175,c_2080])).

cnf(c_3480,plain,
    ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top
    | X0_49 = X1_49
    | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3446,c_1862,c_2206,c_2209,c_3323,c_3444])).

cnf(c_3481,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3480])).

cnf(c_3529,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
    | sK5 = X0_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_3481])).

cnf(c_3540,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK5 = sK4
    | r2_hidden(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3529])).

cnf(c_3525,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK4)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3518,c_2070])).

cnf(c_1808,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2071,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_3149,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3135,c_2071])).

cnf(c_1807,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2072,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_3148,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3135,c_2072])).

cnf(c_1821,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2603,plain,
    ( sK5 != X0_49
    | sK4 != X0_49
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2604,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_1847,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3540,c_3525,c_3512,c_3149,c_3148,c_2604,c_1849,c_1847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.70/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.99  
% 1.70/0.99  ------  iProver source info
% 1.70/0.99  
% 1.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.99  git: non_committed_changes: false
% 1.70/0.99  git: last_make_outside_of_git: false
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    true
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     num_symb
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       true
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    passive
% 1.70/0.99  --sup_prop_simpl_new                    true
% 1.70/0.99  --sup_prop_simpl_given                  true
% 1.70/0.99  --sup_fun_splitting                     false
% 1.70/0.99  --sup_smt_interval                      50000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   []
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_full_bw                           [BwDemod]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         3
% 1.70/0.99  --comb_sup_mult                         2
% 1.70/0.99  --comb_inst_mult                        10
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  ------ Parsing...
% 1.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.70/0.99  ------ Proving...
% 1.70/0.99  ------ Problem Properties 
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  clauses                                 16
% 1.70/0.99  conjectures                             5
% 1.70/0.99  EPR                                     4
% 1.70/0.99  Horn                                    10
% 1.70/0.99  unary                                   0
% 1.70/0.99  binary                                  7
% 1.70/0.99  lits                                    46
% 1.70/0.99  lits eq                                 20
% 1.70/0.99  fd_pure                                 0
% 1.70/0.99  fd_pseudo                               0
% 1.70/0.99  fd_cond                                 0
% 1.70/0.99  fd_pseudo_cond                          2
% 1.70/0.99  AC symbols                              0
% 1.70/0.99  
% 1.70/0.99  ------ Schedule dynamic 5 is on 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  Current options:
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    true
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     none
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       false
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    passive
% 1.70/0.99  --sup_prop_simpl_new                    true
% 1.70/0.99  --sup_prop_simpl_given                  true
% 1.70/0.99  --sup_fun_splitting                     false
% 1.70/0.99  --sup_smt_interval                      50000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   []
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_full_bw                           [BwDemod]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         3
% 1.70/0.99  --comb_sup_mult                         2
% 1.70/0.99  --comb_inst_mult                        10
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ Proving...
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  % SZS status Theorem for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  fof(f5,conjecture,(
% 1.70/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f6,negated_conjecture,(
% 1.70/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.70/0.99    inference(negated_conjecture,[],[f5])).
% 1.70/0.99  
% 1.70/0.99  fof(f13,plain,(
% 1.70/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.70/0.99    inference(ennf_transformation,[],[f6])).
% 1.70/0.99  
% 1.70/0.99  fof(f14,plain,(
% 1.70/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.70/0.99    inference(flattening,[],[f13])).
% 1.70/0.99  
% 1.70/0.99  fof(f20,plain,(
% 1.70/0.99    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.70/0.99    inference(nnf_transformation,[],[f14])).
% 1.70/0.99  
% 1.70/0.99  fof(f21,plain,(
% 1.70/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.70/0.99    inference(flattening,[],[f20])).
% 1.70/0.99  
% 1.70/0.99  fof(f22,plain,(
% 1.70/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.70/0.99    inference(rectify,[],[f21])).
% 1.70/0.99  
% 1.70/0.99  fof(f24,plain,(
% 1.70/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f23,plain,(
% 1.70/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f25,plain,(
% 1.70/0.99    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 1.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f24,f23])).
% 1.70/0.99  
% 1.70/0.99  fof(f40,plain,(
% 1.70/0.99    v1_funct_2(sK3,sK2,sK2)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f4,axiom,(
% 1.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f11,plain,(
% 1.70/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.99    inference(ennf_transformation,[],[f4])).
% 1.70/0.99  
% 1.70/0.99  fof(f12,plain,(
% 1.70/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.99    inference(flattening,[],[f11])).
% 1.70/0.99  
% 1.70/0.99  fof(f19,plain,(
% 1.70/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.99    inference(nnf_transformation,[],[f12])).
% 1.70/0.99  
% 1.70/0.99  fof(f33,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f19])).
% 1.70/0.99  
% 1.70/0.99  fof(f41,plain,(
% 1.70/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f3,axiom,(
% 1.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f10,plain,(
% 1.70/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.99    inference(ennf_transformation,[],[f3])).
% 1.70/0.99  
% 1.70/0.99  fof(f32,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f10])).
% 1.70/0.99  
% 1.70/0.99  fof(f1,axiom,(
% 1.70/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f7,plain,(
% 1.70/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f1])).
% 1.70/0.99  
% 1.70/0.99  fof(f8,plain,(
% 1.70/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.99    inference(flattening,[],[f7])).
% 1.70/0.99  
% 1.70/0.99  fof(f15,plain,(
% 1.70/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.99    inference(nnf_transformation,[],[f8])).
% 1.70/0.99  
% 1.70/0.99  fof(f16,plain,(
% 1.70/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.99    inference(rectify,[],[f15])).
% 1.70/0.99  
% 1.70/0.99  fof(f17,plain,(
% 1.70/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f18,plain,(
% 1.70/0.99    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.70/0.99  
% 1.70/0.99  fof(f29,plain,(
% 1.70/0.99    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f39,plain,(
% 1.70/0.99    v1_funct_1(sK3)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f2,axiom,(
% 1.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f9,plain,(
% 1.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.99    inference(ennf_transformation,[],[f2])).
% 1.70/0.99  
% 1.70/0.99  fof(f31,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f9])).
% 1.70/0.99  
% 1.70/0.99  fof(f45,plain,(
% 1.70/0.99    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f26,plain,(
% 1.70/0.99    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f43,plain,(
% 1.70/0.99    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f28,plain,(
% 1.70/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f30,plain,(
% 1.70/0.99    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f42,plain,(
% 1.70/0.99    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f27,plain,(
% 1.70/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f44,plain,(
% 1.70/0.99    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f46,plain,(
% 1.70/0.99    sK4 != sK5 | ~v2_funct_1(sK3)),
% 1.70/0.99    inference(cnf_transformation,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f34,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f19])).
% 1.70/0.99  
% 1.70/0.99  fof(f51,plain,(
% 1.70/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.70/0.99    inference(equality_resolution,[],[f34])).
% 1.70/0.99  
% 1.70/0.99  cnf(c_19,negated_conjecture,
% 1.70/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 1.70/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_12,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.70/0.99      | k1_xboole_0 = X2 ),
% 1.70/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_18,negated_conjecture,
% 1.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.70/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_235,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | sK3 != X0
% 1.70/0.99      | k1_xboole_0 = X2 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_236,plain,
% 1.70/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 1.70/0.99      | k1_relset_1(X0,X1,sK3) = X0
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | k1_xboole_0 = X1 ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_235]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_594,plain,
% 1.70/0.99      ( k1_relset_1(X0,X1,sK3) = X0
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | sK2 != X0
% 1.70/0.99      | sK2 != X1
% 1.70/0.99      | sK3 != sK3
% 1.70/0.99      | k1_xboole_0 = X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_236]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_595,plain,
% 1.70/0.99      ( k1_relset_1(sK2,sK2,sK3) = sK2
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | k1_xboole_0 = sK2 ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1156,plain,
% 1.70/0.99      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_595]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1796,plain,
% 1.70/0.99      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_1156]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_6,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_271,plain,
% 1.70/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | sK3 != X2 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_272,plain,
% 1.70/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_271]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1805,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_272]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2224,plain,
% 1.70/0.99      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.70/0.99      inference(equality_resolution,[status(thm)],[c_1805]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2290,plain,
% 1.70/0.99      ( k1_relat_1(sK3) = sK2 | sK2 = k1_xboole_0 ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1796,c_2224]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1,plain,
% 1.70/0.99      ( ~ v1_relat_1(X0)
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 1.70/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_20,negated_conjecture,
% 1.70/0.99      ( v1_funct_1(sK3) ),
% 1.70/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_416,plain,
% 1.70/0.99      ( ~ v1_relat_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_417,plain,
% 1.70/0.99      ( ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3)
% 1.70/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1801,plain,
% 1.70/0.99      ( ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3)
% 1.70/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_417]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2077,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1860,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1815,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2206,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1815]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_5,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | v1_relat_1(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_280,plain,
% 1.70/0.99      ( v1_relat_1(X0)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_281,plain,
% 1.70/0.99      ( v1_relat_1(sK3)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1804,plain,
% 1.70/0.99      ( v1_relat_1(sK3)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_281]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2208,plain,
% 1.70/0.99      ( v1_relat_1(sK3)
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2209,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2532,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2077,c_1860,c_2206,c_2209]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_14,negated_conjecture,
% 1.70/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.70/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1809,negated_conjecture,
% 1.70/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2070,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1809]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2539,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 1.70/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2532,c_2070]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_4,plain,
% 1.70/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.70/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.70/0.99      | ~ v1_relat_1(X1)
% 1.70/0.99      | ~ v1_funct_1(X1)
% 1.70/0.99      | ~ v2_funct_1(X1)
% 1.70/0.99      | X0 = X2
% 1.70/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.70/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_442,plain,
% 1.70/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.70/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.70/0.99      | ~ v1_relat_1(X1)
% 1.70/0.99      | ~ v2_funct_1(X1)
% 1.70/0.99      | X2 = X0
% 1.70/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.70/0.99      | sK3 != X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_443,plain,
% 1.70/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.70/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | ~ v2_funct_1(sK3)
% 1.70/0.99      | X0 = X1
% 1.70/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1799,plain,
% 1.70/0.99      ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
% 1.70/0.99      | ~ r2_hidden(X1_49,k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | ~ v2_funct_1(sK3)
% 1.70/0.99      | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/0.99      | X0_49 = X1_49 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_443]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1811,plain,
% 1.70/0.99      ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
% 1.70/0.99      | ~ r2_hidden(X1_49,k1_relat_1(sK3))
% 1.70/0.99      | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/0.99      | X0_49 = X1_49
% 1.70/0.99      | ~ sP0_iProver_split ),
% 1.70/0.99      inference(splitting,
% 1.70/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.70/0.99                [c_1799]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2080,plain,
% 1.70/0.99      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/0.99      | X0_49 = X1_49
% 1.70/0.99      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2553,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
% 1.70/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/0.99      | sK1(sK3) = X0_49
% 1.70/0.99      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2539,c_2080]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2747,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/0.99      | sK1(sK3) = sK0(sK3)
% 1.70/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(equality_resolution,[status(thm)],[c_2553]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2814,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/0.99      | sK1(sK3) = sK0(sK3)
% 1.70/0.99      | sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.70/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2290,c_2747]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_16,negated_conjecture,
% 1.70/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 1.70/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_27,plain,
% 1.70/0.99      ( r2_hidden(sK4,sK2) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2,plain,
% 1.70/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.70/0.99      | ~ v1_relat_1(X0)
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | v2_funct_1(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_403,plain,
% 1.70/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.70/0.99      | ~ v1_relat_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_404,plain,
% 1.70/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_403]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1802,plain,
% 1.70/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_404]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2076,plain,
% 1.70/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_405,plain,
% 1.70/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2488,plain,
% 1.70/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2076,c_405,c_2206,c_2209]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2663,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2290,c_2488]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_0,plain,
% 1.70/0.99      ( ~ v1_relat_1(X0)
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | sK1(X0) != sK0(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_429,plain,
% 1.70/0.99      ( ~ v1_relat_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | sK1(X0) != sK0(X0)
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_430,plain,
% 1.70/0.99      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1800,plain,
% 1.70/0.99      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_430]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1861,plain,
% 1.70/0.99      ( sK1(sK3) != sK0(sK3)
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_17,negated_conjecture,
% 1.70/0.99      ( ~ r2_hidden(X0,sK2)
% 1.70/0.99      | ~ r2_hidden(X1,sK2)
% 1.70/0.99      | v2_funct_1(sK3)
% 1.70/0.99      | X1 = X0
% 1.70/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1806,negated_conjecture,
% 1.70/0.99      ( ~ r2_hidden(X0_49,sK2)
% 1.70/0.99      | ~ r2_hidden(X1_49,sK2)
% 1.70/0.99      | v2_funct_1(sK3)
% 1.70/0.99      | k1_funct_1(sK3,X1_49) != k1_funct_1(sK3,X0_49)
% 1.70/0.99      | X1_49 = X0_49 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2235,plain,
% 1.70/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 1.70/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 1.70/0.99      | v2_funct_1(sK3)
% 1.70/0.99      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.70/0.99      | sK1(sK3) = sK0(sK3) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1806]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2236,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.70/0.99      | sK1(sK3) = sK0(sK3)
% 1.70/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.70/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2235]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3,plain,
% 1.70/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.70/0.99      | ~ v1_relat_1(X0)
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | v2_funct_1(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_390,plain,
% 1.70/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.70/0.99      | ~ v1_relat_1(X0)
% 1.70/0.99      | v2_funct_1(X0)
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_391,plain,
% 1.70/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1803,plain,
% 1.70/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.70/0.99      | ~ v1_relat_1(sK3)
% 1.70/0.99      | v2_funct_1(sK3) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_391]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2075,plain,
% 1.70/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_392,plain,
% 1.70/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2481,plain,
% 1.70/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2075,c_392,c_2206,c_2209]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2664,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(sK0(sK3),sK2) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2290,c_2481]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2853,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0 | v2_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2663,c_1860,c_1861,c_2206,c_2209,c_2236,c_2664]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2860,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) | sK2 = k1_xboole_0 ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2853,c_2070]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2874,plain,
% 1.70/0.99      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
% 1.70/0.99      | sK5 = X0_49
% 1.70/0.99      | sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2860,c_2080]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_15,negated_conjecture,
% 1.70/0.99      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 1.70/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_28,plain,
% 1.70/0.99      ( r2_hidden(sK5,sK2) = iProver_top
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1829,plain,
% 1.70/0.99      ( ~ r2_hidden(X0_49,X0_46)
% 1.70/0.99      | r2_hidden(X1_49,X1_46)
% 1.70/0.99      | X1_49 != X0_49
% 1.70/0.99      | X1_46 != X0_46 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2595,plain,
% 1.70/0.99      ( r2_hidden(X0_49,X0_46)
% 1.70/0.99      | ~ r2_hidden(sK5,sK2)
% 1.70/0.99      | X0_49 != sK5
% 1.70/0.99      | X0_46 != sK2 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1829]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2793,plain,
% 1.70/0.99      ( r2_hidden(sK5,k1_relat_1(sK3))
% 1.70/0.99      | ~ r2_hidden(sK5,sK2)
% 1.70/0.99      | sK5 != sK5
% 1.70/0.99      | k1_relat_1(sK3) != sK2 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_2595]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2794,plain,
% 1.70/0.99      ( sK5 != sK5
% 1.70/0.99      | k1_relat_1(sK3) != sK2
% 1.70/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 1.70/0.99      | r2_hidden(sK5,sK2) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2793]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1812,plain,
% 1.70/0.99      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 1.70/0.99      inference(splitting,
% 1.70/0.99                [splitting(split),new_symbols(definition,[])],
% 1.70/0.99                [c_1799]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2079,plain,
% 1.70/0.99      ( v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top
% 1.70/0.99      | sP0_iProver_split = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1862,plain,
% 1.70/0.99      ( v1_relat_1(sK3) != iProver_top
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top
% 1.70/0.99      | sP0_iProver_split = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2393,plain,
% 1.70/0.99      ( v2_funct_1(sK3) != iProver_top
% 1.70/0.99      | sP0_iProver_split = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2079,c_1862,c_2206,c_2209]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2859,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0 | sP0_iProver_split = iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2853,c_2393]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1817,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2990,plain,
% 1.70/0.99      ( sK5 = sK5 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1817]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3053,plain,
% 1.70/0.99      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
% 1.70/0.99      | sK5 = X0_49
% 1.70/0.99      | sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2874,c_28,c_1860,c_1861,c_2206,c_2209,c_2236,c_2290,
% 1.70/0.99                 c_2663,c_2664,c_2794,c_2859,c_2990]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3065,plain,
% 1.70/0.99      ( sK5 = sK4
% 1.70/0.99      | sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.70/0.99      inference(equality_resolution,[status(thm)],[c_3053]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_13,negated_conjecture,
% 1.70/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.70/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1810,negated_conjecture,
% 1.70/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1849,plain,
% 1.70/0.99      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1850,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 1.70/0.99      | v2_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1809]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2608,plain,
% 1.70/0.99      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 1.70/0.99      | ~ r2_hidden(sK4,k1_relat_1(sK3))
% 1.70/0.99      | ~ sP0_iProver_split
% 1.70/0.99      | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
% 1.70/0.99      | sK4 = sK5 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1811]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2609,plain,
% 1.70/0.99      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
% 1.70/0.99      | sK4 = sK5
% 1.70/0.99      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2608]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3126,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0
% 1.70/0.99      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_3065,c_28,c_1849,c_1850,c_1860,c_1861,c_2206,c_2209,
% 1.70/0.99                 c_2236,c_2290,c_2609,c_2663,c_2664,c_2794,c_2859,c_2990]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3132,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0 | r2_hidden(sK4,sK2) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2290,c_3126]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3135,plain,
% 1.70/0.99      ( sK2 = k1_xboole_0 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2814,c_27,c_2853,c_3132]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3142,plain,
% 1.70/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 1.70/0.99      inference(demodulation,[status(thm)],[c_3135,c_2224]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_11,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.70/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.70/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_327,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.70/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/1.00      | sK3 != X0 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_328,plain,
% 1.70/1.00      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.70/1.00      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.70/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_327]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_619,plain,
% 1.70/1.00      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.70/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/1.00      | sK2 != X0
% 1.70/1.00      | sK2 != k1_xboole_0
% 1.70/1.00      | sK3 != sK3 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_328]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_620,plain,
% 1.70/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.70/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/1.00      | sK2 != k1_xboole_0 ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_619]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1797,plain,
% 1.70/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.70/1.00      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.70/1.00      | sK2 != k1_xboole_0 ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_620]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3146,plain,
% 1.70/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.70/1.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 1.70/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3135,c_1797]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3162,plain,
% 1.70/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 1.70/1.00      inference(equality_resolution_simp,[status(thm)],[c_3146]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3175,plain,
% 1.70/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.70/1.00      inference(light_normalisation,[status(thm)],[c_3142,c_3162]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3444,plain,
% 1.70/1.00      ( r2_hidden(sK1(sK3),k1_xboole_0) = iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3175,c_2488]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2073,plain,
% 1.70/1.00      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/1.00      | X0_49 = X1_49
% 1.70/1.00      | r2_hidden(X0_49,sK2) != iProver_top
% 1.70/1.00      | r2_hidden(X1_49,sK2) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1806]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2554,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
% 1.70/1.00      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/1.00      | sK1(sK3) = X0_49
% 1.70/1.00      | r2_hidden(X0_49,sK2) != iProver_top
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_2539,c_2073]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3141,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_49)
% 1.70/1.00      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/1.00      | sK1(sK3) = X0_49
% 1.70/1.00      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3135,c_2554]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2281,plain,
% 1.70/1.00      ( sK1(sK3) = sK1(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1817]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2314,plain,
% 1.70/1.00      ( sK0(sK3) = sK0(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1817]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2649,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 1.70/1.00      | sK1(sK3) = sK0(sK3)
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.70/1.00      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(equality_resolution,[status(thm)],[c_2554]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2732,plain,
% 1.70/1.00      ( r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.70/1.00      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_2649,c_1860,c_1861,c_2206,c_2209,c_2236]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1819,plain,
% 1.70/1.00      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.70/1.00      theory(equality) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2264,plain,
% 1.70/1.00      ( X0_46 != X1_46 | sK2 != X1_46 | sK2 = X0_46 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1819]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2910,plain,
% 1.70/1.00      ( k1_relat_1(sK3) != X0_46 | sK2 != X0_46 | sK2 = k1_relat_1(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2264]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2912,plain,
% 1.70/1.00      ( k1_relat_1(sK3) != k1_xboole_0
% 1.70/1.00      | sK2 = k1_relat_1(sK3)
% 1.70/1.00      | sK2 != k1_xboole_0 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2910]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2257,plain,
% 1.70/1.00      ( r2_hidden(X0_49,X0_46)
% 1.70/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.70/1.00      | X0_49 != sK0(sK3)
% 1.70/1.00      | X0_46 != k1_relat_1(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1829]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2313,plain,
% 1.70/1.00      ( r2_hidden(sK0(sK3),X0_46)
% 1.70/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.70/1.00      | sK0(sK3) != sK0(sK3)
% 1.70/1.00      | X0_46 != k1_relat_1(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2257]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2911,plain,
% 1.70/1.00      ( ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.70/1.00      | r2_hidden(sK0(sK3),sK2)
% 1.70/1.00      | sK0(sK3) != sK0(sK3)
% 1.70/1.00      | sK2 != k1_relat_1(sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2313]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2913,plain,
% 1.70/1.00      ( sK0(sK3) != sK0(sK3)
% 1.70/1.00      | sK2 != k1_relat_1(sK3)
% 1.70/1.00      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 1.70/1.00      | r2_hidden(sK0(sK3),sK2) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2911]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2954,plain,
% 1.70/1.00      ( ~ r2_hidden(X0_49,X0_46)
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2)
% 1.70/1.00      | sK1(sK3) != X0_49
% 1.70/1.00      | sK2 != X0_46 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1829]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3105,plain,
% 1.70/1.00      ( ~ r2_hidden(sK1(sK3),X0_46)
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2)
% 1.70/1.00      | sK1(sK3) != sK1(sK3)
% 1.70/1.00      | sK2 != X0_46 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2954]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3106,plain,
% 1.70/1.00      ( sK1(sK3) != sK1(sK3)
% 1.70/1.00      | sK2 != X0_46
% 1.70/1.00      | r2_hidden(sK1(sK3),X0_46) != iProver_top
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3105]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3108,plain,
% 1.70/1.00      ( sK1(sK3) != sK1(sK3)
% 1.70/1.00      | sK2 != k1_xboole_0
% 1.70/1.00      | r2_hidden(sK1(sK3),sK2) = iProver_top
% 1.70/1.00      | r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_3106]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3323,plain,
% 1.70/1.00      ( r2_hidden(sK1(sK3),k1_xboole_0) != iProver_top
% 1.70/1.00      | v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_3141,c_27,c_392,c_2206,c_2209,c_2281,c_2314,c_2732,
% 1.70/1.00                 c_2853,c_2912,c_2913,c_3108,c_3132,c_3175]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3512,plain,
% 1.70/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_3444,c_3323]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3518,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_3512,c_2070]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3446,plain,
% 1.70/1.00      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/1.00      | X0_49 = X1_49
% 1.70/1.00      | r2_hidden(X1_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | sP0_iProver_split != iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3175,c_2080]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3480,plain,
% 1.70/1.00      ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(X1_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | X0_49 = X1_49
% 1.70/1.00      | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49) ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_3446,c_1862,c_2206,c_2209,c_3323,c_3444]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3481,plain,
% 1.70/1.00      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.70/1.00      | X0_49 = X1_49
% 1.70/1.00      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(X1_49,k1_xboole_0) != iProver_top ),
% 1.70/1.00      inference(renaming,[status(thm)],[c_3480]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3529,plain,
% 1.70/1.00      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
% 1.70/1.00      | sK5 = X0_49
% 1.70/1.00      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_3518,c_3481]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3540,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
% 1.70/1.00      | sK5 = sK4
% 1.70/1.00      | r2_hidden(sK5,k1_xboole_0) != iProver_top
% 1.70/1.00      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_3529]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3525,plain,
% 1.70/1.00      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK4)
% 1.70/1.00      | v2_funct_1(sK3) != iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3518,c_2070]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1808,negated_conjecture,
% 1.70/1.00      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2071,plain,
% 1.70/1.00      ( r2_hidden(sK5,sK2) = iProver_top
% 1.70/1.00      | v2_funct_1(sK3) != iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3149,plain,
% 1.70/1.00      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 1.70/1.00      | v2_funct_1(sK3) != iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3135,c_2071]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1807,negated_conjecture,
% 1.70/1.00      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2072,plain,
% 1.70/1.00      ( r2_hidden(sK4,sK2) = iProver_top
% 1.70/1.00      | v2_funct_1(sK3) != iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1807]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3148,plain,
% 1.70/1.00      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 1.70/1.00      | v2_funct_1(sK3) != iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3135,c_2072]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1821,plain,
% 1.70/1.00      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.70/1.00      theory(equality) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2603,plain,
% 1.70/1.00      ( sK5 != X0_49 | sK4 != X0_49 | sK4 = sK5 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2604,plain,
% 1.70/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2603]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1847,plain,
% 1.70/1.00      ( sK4 = sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1817]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(contradiction,plain,
% 1.70/1.00      ( $false ),
% 1.70/1.00      inference(minisat,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_3540,c_3525,c_3512,c_3149,c_3148,c_2604,c_1849,c_1847]) ).
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.70/1.00  
% 1.70/1.00  ------                               Statistics
% 1.70/1.00  
% 1.70/1.00  ------ General
% 1.70/1.00  
% 1.70/1.00  abstr_ref_over_cycles:                  0
% 1.70/1.00  abstr_ref_under_cycles:                 0
% 1.70/1.00  gc_basic_clause_elim:                   0
% 1.70/1.00  forced_gc_time:                         0
% 1.70/1.00  parsing_time:                           0.033
% 1.70/1.00  unif_index_cands_time:                  0.
% 1.70/1.00  unif_index_add_time:                    0.
% 1.70/1.00  orderings_time:                         0.
% 1.70/1.00  out_proof_time:                         0.01
% 1.70/1.00  total_time:                             0.122
% 1.70/1.00  num_of_symbols:                         52
% 1.70/1.00  num_of_terms:                           1450
% 1.70/1.00  
% 1.70/1.00  ------ Preprocessing
% 1.70/1.00  
% 1.70/1.00  num_of_splits:                          1
% 1.70/1.00  num_of_split_atoms:                     1
% 1.70/1.00  num_of_reused_defs:                     0
% 1.70/1.00  num_eq_ax_congr_red:                    6
% 1.70/1.00  num_of_sem_filtered_clauses:            1
% 1.70/1.00  num_of_subtypes:                        5
% 1.70/1.00  monotx_restored_types:                  0
% 1.70/1.00  sat_num_of_epr_types:                   0
% 1.70/1.00  sat_num_of_non_cyclic_types:            0
% 1.70/1.00  sat_guarded_non_collapsed_types:        1
% 1.70/1.00  num_pure_diseq_elim:                    0
% 1.70/1.00  simp_replaced_by:                       0
% 1.70/1.00  res_preprocessed:                       107
% 1.70/1.00  prep_upred:                             0
% 1.70/1.00  prep_unflattend:                        29
% 1.70/1.00  smt_new_axioms:                         0
% 1.70/1.00  pred_elim_cands:                        3
% 1.70/1.00  pred_elim:                              3
% 1.70/1.00  pred_elim_cl:                           6
% 1.70/1.00  pred_elim_cycles:                       7
% 1.70/1.00  merged_defs:                            0
% 1.70/1.00  merged_defs_ncl:                        0
% 1.70/1.00  bin_hyper_res:                          0
% 1.70/1.00  prep_cycles:                            4
% 1.70/1.00  pred_elim_time:                         0.022
% 1.70/1.00  splitting_time:                         0.
% 1.70/1.00  sem_filter_time:                        0.
% 1.70/1.00  monotx_time:                            0.
% 1.70/1.00  subtype_inf_time:                       0.
% 1.70/1.00  
% 1.70/1.00  ------ Problem properties
% 1.70/1.00  
% 1.70/1.00  clauses:                                16
% 1.70/1.00  conjectures:                            5
% 1.70/1.00  epr:                                    4
% 1.70/1.00  horn:                                   10
% 1.70/1.00  ground:                                 12
% 1.70/1.00  unary:                                  0
% 1.70/1.00  binary:                                 7
% 1.70/1.00  lits:                                   46
% 1.70/1.00  lits_eq:                                20
% 1.70/1.00  fd_pure:                                0
% 1.70/1.00  fd_pseudo:                              0
% 1.70/1.00  fd_cond:                                0
% 1.70/1.00  fd_pseudo_cond:                         2
% 1.70/1.00  ac_symbols:                             0
% 1.70/1.00  
% 1.70/1.00  ------ Propositional Solver
% 1.70/1.00  
% 1.70/1.00  prop_solver_calls:                      29
% 1.70/1.00  prop_fast_solver_calls:                 1042
% 1.70/1.00  smt_solver_calls:                       0
% 1.70/1.00  smt_fast_solver_calls:                  0
% 1.70/1.00  prop_num_of_clauses:                    717
% 1.70/1.00  prop_preprocess_simplified:             2946
% 1.70/1.00  prop_fo_subsumed:                       27
% 1.70/1.00  prop_solver_time:                       0.
% 1.70/1.00  smt_solver_time:                        0.
% 1.70/1.00  smt_fast_solver_time:                   0.
% 1.70/1.00  prop_fast_solver_time:                  0.
% 1.70/1.00  prop_unsat_core_time:                   0.
% 1.70/1.00  
% 1.70/1.00  ------ QBF
% 1.70/1.00  
% 1.70/1.00  qbf_q_res:                              0
% 1.70/1.00  qbf_num_tautologies:                    0
% 1.70/1.00  qbf_prep_cycles:                        0
% 1.70/1.00  
% 1.70/1.00  ------ BMC1
% 1.70/1.00  
% 1.70/1.00  bmc1_current_bound:                     -1
% 1.70/1.00  bmc1_last_solved_bound:                 -1
% 1.70/1.00  bmc1_unsat_core_size:                   -1
% 1.70/1.00  bmc1_unsat_core_parents_size:           -1
% 1.70/1.00  bmc1_merge_next_fun:                    0
% 1.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.70/1.00  
% 1.70/1.00  ------ Instantiation
% 1.70/1.00  
% 1.70/1.00  inst_num_of_clauses:                    188
% 1.70/1.00  inst_num_in_passive:                    33
% 1.70/1.00  inst_num_in_active:                     144
% 1.70/1.00  inst_num_in_unprocessed:                11
% 1.70/1.00  inst_num_of_loops:                      210
% 1.70/1.00  inst_num_of_learning_restarts:          0
% 1.70/1.00  inst_num_moves_active_passive:          61
% 1.70/1.00  inst_lit_activity:                      0
% 1.70/1.00  inst_lit_activity_moves:                0
% 1.70/1.00  inst_num_tautologies:                   0
% 1.70/1.00  inst_num_prop_implied:                  0
% 1.70/1.00  inst_num_existing_simplified:           0
% 1.70/1.00  inst_num_eq_res_simplified:             0
% 1.70/1.00  inst_num_child_elim:                    0
% 1.70/1.00  inst_num_of_dismatching_blockings:      56
% 1.70/1.00  inst_num_of_non_proper_insts:           269
% 1.70/1.00  inst_num_of_duplicates:                 0
% 1.70/1.00  inst_inst_num_from_inst_to_res:         0
% 1.70/1.00  inst_dismatching_checking_time:         0.
% 1.70/1.00  
% 1.70/1.00  ------ Resolution
% 1.70/1.00  
% 1.70/1.00  res_num_of_clauses:                     0
% 1.70/1.00  res_num_in_passive:                     0
% 1.70/1.00  res_num_in_active:                      0
% 1.70/1.00  res_num_of_loops:                       111
% 1.70/1.00  res_forward_subset_subsumed:            42
% 1.70/1.00  res_backward_subset_subsumed:           0
% 1.70/1.00  res_forward_subsumed:                   0
% 1.70/1.00  res_backward_subsumed:                  0
% 1.70/1.00  res_forward_subsumption_resolution:     0
% 1.70/1.00  res_backward_subsumption_resolution:    0
% 1.70/1.00  res_clause_to_clause_subsumption:       72
% 1.70/1.00  res_orphan_elimination:                 0
% 1.70/1.00  res_tautology_del:                      48
% 1.70/1.00  res_num_eq_res_simplified:              1
% 1.70/1.00  res_num_sel_changes:                    0
% 1.70/1.00  res_moves_from_active_to_pass:          0
% 1.70/1.00  
% 1.70/1.00  ------ Superposition
% 1.70/1.00  
% 1.70/1.00  sup_time_total:                         0.
% 1.70/1.00  sup_time_generating:                    0.
% 1.70/1.00  sup_time_sim_full:                      0.
% 1.70/1.00  sup_time_sim_immed:                     0.
% 1.70/1.00  
% 1.70/1.00  sup_num_of_clauses:                     26
% 1.70/1.00  sup_num_in_active:                      18
% 1.70/1.00  sup_num_in_passive:                     8
% 1.70/1.00  sup_num_of_loops:                       41
% 1.70/1.00  sup_fw_superposition:                   18
% 1.70/1.00  sup_bw_superposition:                   23
% 1.70/1.00  sup_immediate_simplified:               8
% 1.70/1.00  sup_given_eliminated:                   0
% 1.70/1.00  comparisons_done:                       0
% 1.70/1.00  comparisons_avoided:                    9
% 1.70/1.00  
% 1.70/1.00  ------ Simplifications
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  sim_fw_subset_subsumed:                 3
% 1.70/1.00  sim_bw_subset_subsumed:                 7
% 1.70/1.00  sim_fw_subsumed:                        4
% 1.70/1.00  sim_bw_subsumed:                        0
% 1.70/1.00  sim_fw_subsumption_res:                 0
% 1.70/1.00  sim_bw_subsumption_res:                 0
% 1.70/1.00  sim_tautology_del:                      2
% 1.70/1.00  sim_eq_tautology_del:                   10
% 1.70/1.00  sim_eq_res_simp:                        1
% 1.70/1.00  sim_fw_demodulated:                     0
% 1.70/1.00  sim_bw_demodulated:                     19
% 1.70/1.00  sim_light_normalised:                   1
% 1.70/1.00  sim_joinable_taut:                      0
% 1.70/1.00  sim_joinable_simp:                      0
% 1.70/1.00  sim_ac_normalised:                      0
% 1.70/1.00  sim_smt_subsumption:                    0
% 1.70/1.00  
%------------------------------------------------------------------------------
