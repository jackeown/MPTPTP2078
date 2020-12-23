%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:53 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_33)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f36,f35])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_385,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_386,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_2687,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_387,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2893,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2894,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2893])).

cnf(c_3580,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2687,c_27,c_387,c_2894])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_331,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_24,c_22])).

cnf(c_2088,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_335])).

cnf(c_2690,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_3586,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_2690])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2695,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2087,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_335])).

cnf(c_2691,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_3286,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2695,c_2691])).

cnf(c_3587,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_3286])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_56,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_58,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_59,plain,
    ( sK1(X0) != sK0(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_61,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2974,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2975,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2974])).

cnf(c_2693,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2699,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3693,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2693,c_2699])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3938,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_2700])).

cnf(c_4101,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3938,c_27])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4106,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_2703])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_359,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_360,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_2689,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_361,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_3488,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2689,c_27,c_361,c_2894])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_192,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_193])).

cnf(c_2692,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_4299,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3488,c_2692])).

cnf(c_4866,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4106,c_4299])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_372,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_373,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_2688,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_374,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_3481,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2688,c_27,c_374,c_2894])).

cnf(c_4300,plain,
    ( r2_hidden(sK1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3481,c_2692])).

cnf(c_4877,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4106,c_4300])).

cnf(c_4948,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_25,c_27,c_58,c_61,c_2894,c_2975,c_3286,c_4866,c_4877])).

cnf(c_4954,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3586,c_4948])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_76,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_80,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_398,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_399,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_639,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_399,c_17])).

cnf(c_730,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_386,c_17])).

cnf(c_821,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_373,c_17])).

cnf(c_912,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_360,c_17])).

cnf(c_2098,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_2110,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_2086,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_412])).

cnf(c_2091,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2977,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_3085,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_2977])).

cnf(c_2085,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_412])).

cnf(c_3815,plain,
    ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_3817,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3815])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2697,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3590,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3580,c_2697])).

cnf(c_2694,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3945,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3590,c_2694])).

cnf(c_627,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) != sK0(sK3) ),
    inference(resolution,[status(thm)],[c_399,c_18])).

cnf(c_809,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_373,c_18])).

cnf(c_810,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_900,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_360,c_18])).

cnf(c_901,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_2684,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2086])).

cnf(c_2118,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2086])).

cnf(c_2928,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2684,c_27,c_2118,c_2894])).

cnf(c_3816,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0)
    | r2_hidden(sK1(X0),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3815])).

cnf(c_3818,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3816])).

cnf(c_4062,plain,
    ( r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | sK1(sK3) = X0
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3945,c_22,c_27,c_76,c_80,c_627,c_810,c_901,c_2110,c_2893,c_2894,c_2928,c_3085,c_3590,c_3818])).

cnf(c_4063,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4062])).

cnf(c_4074,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4063])).

cnf(c_5110,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4074,c_25,c_22,c_27,c_58,c_61,c_76,c_80,c_627,c_810,c_901,c_2110,c_2118,c_2893,c_2894,c_2975,c_3085,c_3590,c_3818,c_4866,c_4877])).

cnf(c_5131,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5110,c_2694])).

cnf(c_5159,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5131,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877])).

cnf(c_5161,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5159])).

cnf(c_5164,plain,
    ( sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_2690])).

cnf(c_5295,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5164,c_4948])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2696,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3285,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2696,c_2691])).

cnf(c_3588,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_3285])).

cnf(c_4956,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3588,c_25,c_27,c_58,c_61,c_2894,c_2975,c_3285,c_4866,c_4877])).

cnf(c_5113,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_5110,c_4956])).

cnf(c_5417,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5164,c_5113])).

cnf(c_5876,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_5295,c_5417])).

cnf(c_5878,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4954,c_22,c_76,c_80,c_639,c_730,c_821,c_912,c_2110,c_2086,c_2893,c_3085,c_3817,c_5161,c_5876])).

cnf(c_5895,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5878,c_2696])).

cnf(c_6066,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5895,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877])).

cnf(c_6071,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_2692])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4297,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2696,c_2692])).

cnf(c_5885,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5878,c_4297])).

cnf(c_6587,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6071,c_25,c_27,c_58,c_61,c_72,c_2894,c_2975,c_4866,c_4877,c_5885])).

cnf(c_2685,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2085])).

cnf(c_5130,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5110,c_2685])).

cnf(c_5192,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK5 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5130,c_25,c_27,c_58,c_61,c_2118,c_2894,c_2975,c_4866,c_4877])).

cnf(c_5193,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5192])).

cnf(c_5204,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5193])).

cnf(c_5778,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_25,c_27,c_33,c_34,c_58,c_61,c_2118,c_2894,c_2975,c_3773,c_4866,c_4877])).

cnf(c_6595,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6587,c_5778])).

cnf(c_5896,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5878,c_2695])).

cnf(c_6186,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5896,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877])).

cnf(c_6191,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6186,c_2692])).

cnf(c_4298,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2695,c_2692])).

cnf(c_5884,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5878,c_4298])).

cnf(c_6609,plain,
    ( r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_25,c_27,c_58,c_61,c_72,c_2894,c_2975,c_4866,c_4877,c_5884])).

cnf(c_7065,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6595,c_6609])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.95/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/0.99  
% 2.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/0.99  
% 2.95/0.99  ------  iProver source info
% 2.95/0.99  
% 2.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/0.99  git: non_committed_changes: false
% 2.95/0.99  git: last_make_outside_of_git: false
% 2.95/0.99  
% 2.95/0.99  ------ 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options
% 2.95/0.99  
% 2.95/0.99  --out_options                           all
% 2.95/0.99  --tptp_safe_out                         true
% 2.95/0.99  --problem_path                          ""
% 2.95/0.99  --include_path                          ""
% 2.95/0.99  --clausifier                            res/vclausify_rel
% 2.95/0.99  --clausifier_options                    --mode clausify
% 2.95/0.99  --stdin                                 false
% 2.95/0.99  --stats_out                             all
% 2.95/0.99  
% 2.95/0.99  ------ General Options
% 2.95/0.99  
% 2.95/0.99  --fof                                   false
% 2.95/0.99  --time_out_real                         305.
% 2.95/0.99  --time_out_virtual                      -1.
% 2.95/0.99  --symbol_type_check                     false
% 2.95/0.99  --clausify_out                          false
% 2.95/0.99  --sig_cnt_out                           false
% 2.95/0.99  --trig_cnt_out                          false
% 2.95/0.99  --trig_cnt_out_tolerance                1.
% 2.95/0.99  --trig_cnt_out_sk_spl                   false
% 2.95/0.99  --abstr_cl_out                          false
% 2.95/0.99  
% 2.95/0.99  ------ Global Options
% 2.95/0.99  
% 2.95/0.99  --schedule                              default
% 2.95/0.99  --add_important_lit                     false
% 2.95/0.99  --prop_solver_per_cl                    1000
% 2.95/0.99  --min_unsat_core                        false
% 2.95/0.99  --soft_assumptions                      false
% 2.95/0.99  --soft_lemma_size                       3
% 2.95/0.99  --prop_impl_unit_size                   0
% 2.95/0.99  --prop_impl_unit                        []
% 2.95/0.99  --share_sel_clauses                     true
% 2.95/0.99  --reset_solvers                         false
% 2.95/0.99  --bc_imp_inh                            [conj_cone]
% 2.95/0.99  --conj_cone_tolerance                   3.
% 2.95/0.99  --extra_neg_conj                        none
% 2.95/0.99  --large_theory_mode                     true
% 2.95/0.99  --prolific_symb_bound                   200
% 2.95/0.99  --lt_threshold                          2000
% 2.95/0.99  --clause_weak_htbl                      true
% 2.95/0.99  --gc_record_bc_elim                     false
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing Options
% 2.95/0.99  
% 2.95/0.99  --preprocessing_flag                    true
% 2.95/0.99  --time_out_prep_mult                    0.1
% 2.95/0.99  --splitting_mode                        input
% 2.95/0.99  --splitting_grd                         true
% 2.95/0.99  --splitting_cvd                         false
% 2.95/0.99  --splitting_cvd_svl                     false
% 2.95/0.99  --splitting_nvd                         32
% 2.95/0.99  --sub_typing                            true
% 2.95/0.99  --prep_gs_sim                           true
% 2.95/0.99  --prep_unflatten                        true
% 2.95/0.99  --prep_res_sim                          true
% 2.95/0.99  --prep_upred                            true
% 2.95/0.99  --prep_sem_filter                       exhaustive
% 2.95/0.99  --prep_sem_filter_out                   false
% 2.95/0.99  --pred_elim                             true
% 2.95/0.99  --res_sim_input                         true
% 2.95/0.99  --eq_ax_congr_red                       true
% 2.95/0.99  --pure_diseq_elim                       true
% 2.95/0.99  --brand_transform                       false
% 2.95/0.99  --non_eq_to_eq                          false
% 2.95/0.99  --prep_def_merge                        true
% 2.95/0.99  --prep_def_merge_prop_impl              false
% 2.95/0.99  --prep_def_merge_mbd                    true
% 2.95/0.99  --prep_def_merge_tr_red                 false
% 2.95/0.99  --prep_def_merge_tr_cl                  false
% 2.95/0.99  --smt_preprocessing                     true
% 2.95/0.99  --smt_ac_axioms                         fast
% 2.95/0.99  --preprocessed_out                      false
% 2.95/0.99  --preprocessed_stats                    false
% 2.95/0.99  
% 2.95/0.99  ------ Abstraction refinement Options
% 2.95/0.99  
% 2.95/0.99  --abstr_ref                             []
% 2.95/0.99  --abstr_ref_prep                        false
% 2.95/0.99  --abstr_ref_until_sat                   false
% 2.95/0.99  --abstr_ref_sig_restrict                funpre
% 2.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/0.99  --abstr_ref_under                       []
% 2.95/0.99  
% 2.95/0.99  ------ SAT Options
% 2.95/0.99  
% 2.95/0.99  --sat_mode                              false
% 2.95/0.99  --sat_fm_restart_options                ""
% 2.95/0.99  --sat_gr_def                            false
% 2.95/0.99  --sat_epr_types                         true
% 2.95/0.99  --sat_non_cyclic_types                  false
% 2.95/0.99  --sat_finite_models                     false
% 2.95/0.99  --sat_fm_lemmas                         false
% 2.95/0.99  --sat_fm_prep                           false
% 2.95/0.99  --sat_fm_uc_incr                        true
% 2.95/0.99  --sat_out_model                         small
% 2.95/0.99  --sat_out_clauses                       false
% 2.95/0.99  
% 2.95/0.99  ------ QBF Options
% 2.95/0.99  
% 2.95/0.99  --qbf_mode                              false
% 2.95/0.99  --qbf_elim_univ                         false
% 2.95/0.99  --qbf_dom_inst                          none
% 2.95/0.99  --qbf_dom_pre_inst                      false
% 2.95/0.99  --qbf_sk_in                             false
% 2.95/0.99  --qbf_pred_elim                         true
% 2.95/0.99  --qbf_split                             512
% 2.95/0.99  
% 2.95/0.99  ------ BMC1 Options
% 2.95/0.99  
% 2.95/0.99  --bmc1_incremental                      false
% 2.95/0.99  --bmc1_axioms                           reachable_all
% 2.95/0.99  --bmc1_min_bound                        0
% 2.95/0.99  --bmc1_max_bound                        -1
% 2.95/0.99  --bmc1_max_bound_default                -1
% 2.95/0.99  --bmc1_symbol_reachability              true
% 2.95/0.99  --bmc1_property_lemmas                  false
% 2.95/0.99  --bmc1_k_induction                      false
% 2.95/0.99  --bmc1_non_equiv_states                 false
% 2.95/0.99  --bmc1_deadlock                         false
% 2.95/0.99  --bmc1_ucm                              false
% 2.95/0.99  --bmc1_add_unsat_core                   none
% 2.95/0.99  --bmc1_unsat_core_children              false
% 2.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/0.99  --bmc1_out_stat                         full
% 2.95/0.99  --bmc1_ground_init                      false
% 2.95/0.99  --bmc1_pre_inst_next_state              false
% 2.95/0.99  --bmc1_pre_inst_state                   false
% 2.95/0.99  --bmc1_pre_inst_reach_state             false
% 2.95/0.99  --bmc1_out_unsat_core                   false
% 2.95/0.99  --bmc1_aig_witness_out                  false
% 2.95/0.99  --bmc1_verbose                          false
% 2.95/0.99  --bmc1_dump_clauses_tptp                false
% 2.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.95/0.99  --bmc1_dump_file                        -
% 2.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.95/0.99  --bmc1_ucm_extend_mode                  1
% 2.95/0.99  --bmc1_ucm_init_mode                    2
% 2.95/0.99  --bmc1_ucm_cone_mode                    none
% 2.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.95/0.99  --bmc1_ucm_relax_model                  4
% 2.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/0.99  --bmc1_ucm_layered_model                none
% 2.95/0.99  --bmc1_ucm_max_lemma_size               10
% 2.95/0.99  
% 2.95/0.99  ------ AIG Options
% 2.95/0.99  
% 2.95/0.99  --aig_mode                              false
% 2.95/0.99  
% 2.95/0.99  ------ Instantiation Options
% 2.95/0.99  
% 2.95/0.99  --instantiation_flag                    true
% 2.95/0.99  --inst_sos_flag                         false
% 2.95/0.99  --inst_sos_phase                        true
% 2.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel_side                     num_symb
% 2.95/0.99  --inst_solver_per_active                1400
% 2.95/0.99  --inst_solver_calls_frac                1.
% 2.95/0.99  --inst_passive_queue_type               priority_queues
% 2.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/0.99  --inst_passive_queues_freq              [25;2]
% 2.95/0.99  --inst_dismatching                      true
% 2.95/0.99  --inst_eager_unprocessed_to_passive     true
% 2.95/0.99  --inst_prop_sim_given                   true
% 2.95/0.99  --inst_prop_sim_new                     false
% 2.95/0.99  --inst_subs_new                         false
% 2.95/0.99  --inst_eq_res_simp                      false
% 2.95/0.99  --inst_subs_given                       false
% 2.95/0.99  --inst_orphan_elimination               true
% 2.95/0.99  --inst_learning_loop_flag               true
% 2.95/0.99  --inst_learning_start                   3000
% 2.95/0.99  --inst_learning_factor                  2
% 2.95/0.99  --inst_start_prop_sim_after_learn       3
% 2.95/0.99  --inst_sel_renew                        solver
% 2.95/0.99  --inst_lit_activity_flag                true
% 2.95/0.99  --inst_restr_to_given                   false
% 2.95/0.99  --inst_activity_threshold               500
% 2.95/0.99  --inst_out_proof                        true
% 2.95/0.99  
% 2.95/0.99  ------ Resolution Options
% 2.95/0.99  
% 2.95/0.99  --resolution_flag                       true
% 2.95/0.99  --res_lit_sel                           adaptive
% 2.95/0.99  --res_lit_sel_side                      none
% 2.95/0.99  --res_ordering                          kbo
% 2.95/0.99  --res_to_prop_solver                    active
% 2.95/0.99  --res_prop_simpl_new                    false
% 2.95/0.99  --res_prop_simpl_given                  true
% 2.95/0.99  --res_passive_queue_type                priority_queues
% 2.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/0.99  --res_passive_queues_freq               [15;5]
% 2.95/0.99  --res_forward_subs                      full
% 2.95/0.99  --res_backward_subs                     full
% 2.95/0.99  --res_forward_subs_resolution           true
% 2.95/0.99  --res_backward_subs_resolution          true
% 2.95/0.99  --res_orphan_elimination                true
% 2.95/0.99  --res_time_limit                        2.
% 2.95/0.99  --res_out_proof                         true
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Options
% 2.95/0.99  
% 2.95/0.99  --superposition_flag                    true
% 2.95/0.99  --sup_passive_queue_type                priority_queues
% 2.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.95/0.99  --demod_completeness_check              fast
% 2.95/0.99  --demod_use_ground                      true
% 2.95/0.99  --sup_to_prop_solver                    passive
% 2.95/0.99  --sup_prop_simpl_new                    true
% 2.95/0.99  --sup_prop_simpl_given                  true
% 2.95/0.99  --sup_fun_splitting                     false
% 2.95/0.99  --sup_smt_interval                      50000
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Simplification Setup
% 2.95/0.99  
% 2.95/0.99  --sup_indices_passive                   []
% 2.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_full_bw                           [BwDemod]
% 2.95/0.99  --sup_immed_triv                        [TrivRules]
% 2.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_immed_bw_main                     []
% 2.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  
% 2.95/0.99  ------ Combination Options
% 2.95/0.99  
% 2.95/0.99  --comb_res_mult                         3
% 2.95/0.99  --comb_sup_mult                         2
% 2.95/0.99  --comb_inst_mult                        10
% 2.95/0.99  
% 2.95/0.99  ------ Debug Options
% 2.95/0.99  
% 2.95/0.99  --dbg_backtrace                         false
% 2.95/0.99  --dbg_dump_prop_clauses                 false
% 2.95/0.99  --dbg_dump_prop_clauses_file            -
% 2.95/0.99  --dbg_out_stat                          false
% 2.95/0.99  ------ Parsing...
% 2.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/0.99  ------ Proving...
% 2.95/0.99  ------ Problem Properties 
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  clauses                                 24
% 2.95/0.99  conjectures                             6
% 2.95/0.99  EPR                                     9
% 2.95/0.99  Horn                                    19
% 2.95/0.99  unary                                   3
% 2.95/0.99  binary                                  9
% 2.95/0.99  lits                                    61
% 2.95/0.99  lits eq                                 12
% 2.95/0.99  fd_pure                                 0
% 2.95/0.99  fd_pseudo                               0
% 2.95/0.99  fd_cond                                 0
% 2.95/0.99  fd_pseudo_cond                          3
% 2.95/0.99  AC symbols                              0
% 2.95/0.99  
% 2.95/0.99  ------ Schedule dynamic 5 is on 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  ------ 
% 2.95/0.99  Current options:
% 2.95/0.99  ------ 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options
% 2.95/0.99  
% 2.95/0.99  --out_options                           all
% 2.95/0.99  --tptp_safe_out                         true
% 2.95/0.99  --problem_path                          ""
% 2.95/0.99  --include_path                          ""
% 2.95/0.99  --clausifier                            res/vclausify_rel
% 2.95/0.99  --clausifier_options                    --mode clausify
% 2.95/0.99  --stdin                                 false
% 2.95/0.99  --stats_out                             all
% 2.95/0.99  
% 2.95/0.99  ------ General Options
% 2.95/0.99  
% 2.95/0.99  --fof                                   false
% 2.95/0.99  --time_out_real                         305.
% 2.95/0.99  --time_out_virtual                      -1.
% 2.95/0.99  --symbol_type_check                     false
% 2.95/0.99  --clausify_out                          false
% 2.95/0.99  --sig_cnt_out                           false
% 2.95/0.99  --trig_cnt_out                          false
% 2.95/0.99  --trig_cnt_out_tolerance                1.
% 2.95/0.99  --trig_cnt_out_sk_spl                   false
% 2.95/0.99  --abstr_cl_out                          false
% 2.95/0.99  
% 2.95/0.99  ------ Global Options
% 2.95/0.99  
% 2.95/0.99  --schedule                              default
% 2.95/0.99  --add_important_lit                     false
% 2.95/0.99  --prop_solver_per_cl                    1000
% 2.95/0.99  --min_unsat_core                        false
% 2.95/0.99  --soft_assumptions                      false
% 2.95/0.99  --soft_lemma_size                       3
% 2.95/0.99  --prop_impl_unit_size                   0
% 2.95/0.99  --prop_impl_unit                        []
% 2.95/0.99  --share_sel_clauses                     true
% 2.95/0.99  --reset_solvers                         false
% 2.95/0.99  --bc_imp_inh                            [conj_cone]
% 2.95/0.99  --conj_cone_tolerance                   3.
% 2.95/0.99  --extra_neg_conj                        none
% 2.95/0.99  --large_theory_mode                     true
% 2.95/0.99  --prolific_symb_bound                   200
% 2.95/0.99  --lt_threshold                          2000
% 2.95/0.99  --clause_weak_htbl                      true
% 2.95/0.99  --gc_record_bc_elim                     false
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing Options
% 2.95/0.99  
% 2.95/0.99  --preprocessing_flag                    true
% 2.95/0.99  --time_out_prep_mult                    0.1
% 2.95/0.99  --splitting_mode                        input
% 2.95/0.99  --splitting_grd                         true
% 2.95/0.99  --splitting_cvd                         false
% 2.95/0.99  --splitting_cvd_svl                     false
% 2.95/0.99  --splitting_nvd                         32
% 2.95/0.99  --sub_typing                            true
% 2.95/0.99  --prep_gs_sim                           true
% 2.95/0.99  --prep_unflatten                        true
% 2.95/0.99  --prep_res_sim                          true
% 2.95/0.99  --prep_upred                            true
% 2.95/0.99  --prep_sem_filter                       exhaustive
% 2.95/0.99  --prep_sem_filter_out                   false
% 2.95/0.99  --pred_elim                             true
% 2.95/0.99  --res_sim_input                         true
% 2.95/0.99  --eq_ax_congr_red                       true
% 2.95/0.99  --pure_diseq_elim                       true
% 2.95/0.99  --brand_transform                       false
% 2.95/0.99  --non_eq_to_eq                          false
% 2.95/0.99  --prep_def_merge                        true
% 2.95/0.99  --prep_def_merge_prop_impl              false
% 2.95/0.99  --prep_def_merge_mbd                    true
% 2.95/0.99  --prep_def_merge_tr_red                 false
% 2.95/0.99  --prep_def_merge_tr_cl                  false
% 2.95/0.99  --smt_preprocessing                     true
% 2.95/0.99  --smt_ac_axioms                         fast
% 2.95/0.99  --preprocessed_out                      false
% 2.95/0.99  --preprocessed_stats                    false
% 2.95/0.99  
% 2.95/0.99  ------ Abstraction refinement Options
% 2.95/0.99  
% 2.95/0.99  --abstr_ref                             []
% 2.95/0.99  --abstr_ref_prep                        false
% 2.95/0.99  --abstr_ref_until_sat                   false
% 2.95/0.99  --abstr_ref_sig_restrict                funpre
% 2.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/0.99  --abstr_ref_under                       []
% 2.95/0.99  
% 2.95/0.99  ------ SAT Options
% 2.95/0.99  
% 2.95/0.99  --sat_mode                              false
% 2.95/0.99  --sat_fm_restart_options                ""
% 2.95/0.99  --sat_gr_def                            false
% 2.95/0.99  --sat_epr_types                         true
% 2.95/0.99  --sat_non_cyclic_types                  false
% 2.95/0.99  --sat_finite_models                     false
% 2.95/0.99  --sat_fm_lemmas                         false
% 2.95/0.99  --sat_fm_prep                           false
% 2.95/0.99  --sat_fm_uc_incr                        true
% 2.95/0.99  --sat_out_model                         small
% 2.95/0.99  --sat_out_clauses                       false
% 2.95/0.99  
% 2.95/0.99  ------ QBF Options
% 2.95/0.99  
% 2.95/0.99  --qbf_mode                              false
% 2.95/0.99  --qbf_elim_univ                         false
% 2.95/0.99  --qbf_dom_inst                          none
% 2.95/0.99  --qbf_dom_pre_inst                      false
% 2.95/0.99  --qbf_sk_in                             false
% 2.95/0.99  --qbf_pred_elim                         true
% 2.95/0.99  --qbf_split                             512
% 2.95/0.99  
% 2.95/0.99  ------ BMC1 Options
% 2.95/0.99  
% 2.95/0.99  --bmc1_incremental                      false
% 2.95/0.99  --bmc1_axioms                           reachable_all
% 2.95/0.99  --bmc1_min_bound                        0
% 2.95/0.99  --bmc1_max_bound                        -1
% 2.95/0.99  --bmc1_max_bound_default                -1
% 2.95/0.99  --bmc1_symbol_reachability              true
% 2.95/0.99  --bmc1_property_lemmas                  false
% 2.95/0.99  --bmc1_k_induction                      false
% 2.95/0.99  --bmc1_non_equiv_states                 false
% 2.95/0.99  --bmc1_deadlock                         false
% 2.95/0.99  --bmc1_ucm                              false
% 2.95/0.99  --bmc1_add_unsat_core                   none
% 2.95/0.99  --bmc1_unsat_core_children              false
% 2.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/0.99  --bmc1_out_stat                         full
% 2.95/0.99  --bmc1_ground_init                      false
% 2.95/0.99  --bmc1_pre_inst_next_state              false
% 2.95/0.99  --bmc1_pre_inst_state                   false
% 2.95/0.99  --bmc1_pre_inst_reach_state             false
% 2.95/0.99  --bmc1_out_unsat_core                   false
% 2.95/0.99  --bmc1_aig_witness_out                  false
% 2.95/0.99  --bmc1_verbose                          false
% 2.95/0.99  --bmc1_dump_clauses_tptp                false
% 2.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.95/0.99  --bmc1_dump_file                        -
% 2.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.95/0.99  --bmc1_ucm_extend_mode                  1
% 2.95/0.99  --bmc1_ucm_init_mode                    2
% 2.95/0.99  --bmc1_ucm_cone_mode                    none
% 2.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.95/0.99  --bmc1_ucm_relax_model                  4
% 2.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/0.99  --bmc1_ucm_layered_model                none
% 2.95/0.99  --bmc1_ucm_max_lemma_size               10
% 2.95/0.99  
% 2.95/0.99  ------ AIG Options
% 2.95/0.99  
% 2.95/0.99  --aig_mode                              false
% 2.95/0.99  
% 2.95/0.99  ------ Instantiation Options
% 2.95/0.99  
% 2.95/0.99  --instantiation_flag                    true
% 2.95/0.99  --inst_sos_flag                         false
% 2.95/0.99  --inst_sos_phase                        true
% 2.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel_side                     none
% 2.95/0.99  --inst_solver_per_active                1400
% 2.95/0.99  --inst_solver_calls_frac                1.
% 2.95/0.99  --inst_passive_queue_type               priority_queues
% 2.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/0.99  --inst_passive_queues_freq              [25;2]
% 2.95/0.99  --inst_dismatching                      true
% 2.95/0.99  --inst_eager_unprocessed_to_passive     true
% 2.95/0.99  --inst_prop_sim_given                   true
% 2.95/0.99  --inst_prop_sim_new                     false
% 2.95/0.99  --inst_subs_new                         false
% 2.95/0.99  --inst_eq_res_simp                      false
% 2.95/0.99  --inst_subs_given                       false
% 2.95/0.99  --inst_orphan_elimination               true
% 2.95/0.99  --inst_learning_loop_flag               true
% 2.95/0.99  --inst_learning_start                   3000
% 2.95/0.99  --inst_learning_factor                  2
% 2.95/0.99  --inst_start_prop_sim_after_learn       3
% 2.95/0.99  --inst_sel_renew                        solver
% 2.95/0.99  --inst_lit_activity_flag                true
% 2.95/0.99  --inst_restr_to_given                   false
% 2.95/0.99  --inst_activity_threshold               500
% 2.95/0.99  --inst_out_proof                        true
% 2.95/0.99  
% 2.95/0.99  ------ Resolution Options
% 2.95/0.99  
% 2.95/0.99  --resolution_flag                       false
% 2.95/0.99  --res_lit_sel                           adaptive
% 2.95/0.99  --res_lit_sel_side                      none
% 2.95/0.99  --res_ordering                          kbo
% 2.95/0.99  --res_to_prop_solver                    active
% 2.95/0.99  --res_prop_simpl_new                    false
% 2.95/0.99  --res_prop_simpl_given                  true
% 2.95/0.99  --res_passive_queue_type                priority_queues
% 2.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/0.99  --res_passive_queues_freq               [15;5]
% 2.95/0.99  --res_forward_subs                      full
% 2.95/0.99  --res_backward_subs                     full
% 2.95/0.99  --res_forward_subs_resolution           true
% 2.95/0.99  --res_backward_subs_resolution          true
% 2.95/0.99  --res_orphan_elimination                true
% 2.95/0.99  --res_time_limit                        2.
% 2.95/0.99  --res_out_proof                         true
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Options
% 2.95/0.99  
% 2.95/0.99  --superposition_flag                    true
% 2.95/0.99  --sup_passive_queue_type                priority_queues
% 2.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.95/0.99  --demod_completeness_check              fast
% 2.95/0.99  --demod_use_ground                      true
% 2.95/0.99  --sup_to_prop_solver                    passive
% 2.95/0.99  --sup_prop_simpl_new                    true
% 2.95/0.99  --sup_prop_simpl_given                  true
% 2.95/0.99  --sup_fun_splitting                     false
% 2.95/0.99  --sup_smt_interval                      50000
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Simplification Setup
% 2.95/0.99  
% 2.95/0.99  --sup_indices_passive                   []
% 2.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_full_bw                           [BwDemod]
% 2.95/0.99  --sup_immed_triv                        [TrivRules]
% 2.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_immed_bw_main                     []
% 2.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  
% 2.95/0.99  ------ Combination Options
% 2.95/0.99  
% 2.95/0.99  --comb_res_mult                         3
% 2.95/0.99  --comb_sup_mult                         2
% 2.95/0.99  --comb_inst_mult                        10
% 2.95/0.99  
% 2.95/0.99  ------ Debug Options
% 2.95/0.99  
% 2.95/0.99  --dbg_backtrace                         false
% 2.95/0.99  --dbg_dump_prop_clauses                 false
% 2.95/0.99  --dbg_dump_prop_clauses_file            -
% 2.95/0.99  --dbg_out_stat                          false
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  ------ Proving...
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  % SZS status Theorem for theBenchmark.p
% 2.95/0.99  
% 2.95/0.99   Resolution empty clause
% 2.95/0.99  
% 2.95/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/0.99  
% 2.95/0.99  fof(f6,axiom,(
% 2.95/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f16,plain,(
% 2.95/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.95/0.99    inference(ennf_transformation,[],[f6])).
% 2.95/0.99  
% 2.95/0.99  fof(f17,plain,(
% 2.95/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.99    inference(flattening,[],[f16])).
% 2.95/0.99  
% 2.95/0.99  fof(f28,plain,(
% 2.95/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.99    inference(nnf_transformation,[],[f17])).
% 2.95/0.99  
% 2.95/0.99  fof(f29,plain,(
% 2.95/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.99    inference(rectify,[],[f28])).
% 2.95/0.99  
% 2.95/0.99  fof(f30,plain,(
% 2.95/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.95/0.99    introduced(choice_axiom,[])).
% 2.95/0.99  
% 2.95/0.99  fof(f31,plain,(
% 2.95/0.99    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 2.95/0.99  
% 2.95/0.99  fof(f49,plain,(
% 2.95/0.99    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f31])).
% 2.95/0.99  
% 2.95/0.99  fof(f11,conjecture,(
% 2.95/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f12,negated_conjecture,(
% 2.95/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.95/0.99    inference(negated_conjecture,[],[f11])).
% 2.95/0.99  
% 2.95/0.99  fof(f23,plain,(
% 2.95/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.95/0.99    inference(ennf_transformation,[],[f12])).
% 2.95/0.99  
% 2.95/0.99  fof(f24,plain,(
% 2.95/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.95/0.99    inference(flattening,[],[f23])).
% 2.95/0.99  
% 2.95/0.99  fof(f32,plain,(
% 2.95/0.99    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.95/0.99    inference(nnf_transformation,[],[f24])).
% 2.95/0.99  
% 2.95/0.99  fof(f33,plain,(
% 2.95/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.95/0.99    inference(flattening,[],[f32])).
% 2.95/0.99  
% 2.95/0.99  fof(f34,plain,(
% 2.95/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.95/0.99    inference(rectify,[],[f33])).
% 2.95/0.99  
% 2.95/0.99  fof(f36,plain,(
% 2.95/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.95/0.99    introduced(choice_axiom,[])).
% 2.95/0.99  
% 2.95/0.99  fof(f35,plain,(
% 2.95/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.95/0.99    introduced(choice_axiom,[])).
% 2.95/0.99  
% 2.95/0.99  fof(f37,plain,(
% 2.95/0.99    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f36,f35])).
% 2.95/0.99  
% 2.95/0.99  fof(f55,plain,(
% 2.95/0.99    v1_funct_1(sK3)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f57,plain,(
% 2.95/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f7,axiom,(
% 2.95/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f18,plain,(
% 2.95/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.99    inference(ennf_transformation,[],[f7])).
% 2.95/0.99  
% 2.95/0.99  fof(f51,plain,(
% 2.95/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f18])).
% 2.95/0.99  
% 2.95/0.99  fof(f10,axiom,(
% 2.95/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f21,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.95/0.99    inference(ennf_transformation,[],[f10])).
% 2.95/0.99  
% 2.95/0.99  fof(f22,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.95/0.99    inference(flattening,[],[f21])).
% 2.95/0.99  
% 2.95/0.99  fof(f54,plain,(
% 2.95/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f22])).
% 2.95/0.99  
% 2.95/0.99  fof(f56,plain,(
% 2.95/0.99    v1_funct_2(sK3,sK2,sK2)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f59,plain,(
% 2.95/0.99    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f50,plain,(
% 2.95/0.99    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f31])).
% 2.95/0.99  
% 2.95/0.99  fof(f58,plain,(
% 2.95/0.99    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f9,axiom,(
% 2.95/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f20,plain,(
% 2.95/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.99    inference(ennf_transformation,[],[f9])).
% 2.95/0.99  
% 2.95/0.99  fof(f53,plain,(
% 2.95/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f20])).
% 2.95/0.99  
% 2.95/0.99  fof(f8,axiom,(
% 2.95/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f19,plain,(
% 2.95/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.99    inference(ennf_transformation,[],[f8])).
% 2.95/0.99  
% 2.95/0.99  fof(f52,plain,(
% 2.95/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f19])).
% 2.95/0.99  
% 2.95/0.99  fof(f4,axiom,(
% 2.95/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f27,plain,(
% 2.95/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.95/0.99    inference(nnf_transformation,[],[f4])).
% 2.95/0.99  
% 2.95/0.99  fof(f43,plain,(
% 2.95/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f27])).
% 2.95/0.99  
% 2.95/0.99  fof(f47,plain,(
% 2.95/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f31])).
% 2.95/0.99  
% 2.95/0.99  fof(f3,axiom,(
% 2.95/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f13,plain,(
% 2.95/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.95/0.99    inference(ennf_transformation,[],[f3])).
% 2.95/0.99  
% 2.95/0.99  fof(f42,plain,(
% 2.95/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f13])).
% 2.95/0.99  
% 2.95/0.99  fof(f44,plain,(
% 2.95/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f27])).
% 2.95/0.99  
% 2.95/0.99  fof(f48,plain,(
% 2.95/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f31])).
% 2.95/0.99  
% 2.95/0.99  fof(f1,axiom,(
% 2.95/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f25,plain,(
% 2.95/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/0.99    inference(nnf_transformation,[],[f1])).
% 2.95/0.99  
% 2.95/0.99  fof(f26,plain,(
% 2.95/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/0.99    inference(flattening,[],[f25])).
% 2.95/0.99  
% 2.95/0.99  fof(f38,plain,(
% 2.95/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.95/0.99    inference(cnf_transformation,[],[f26])).
% 2.95/0.99  
% 2.95/0.99  fof(f64,plain,(
% 2.95/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.95/0.99    inference(equality_resolution,[],[f38])).
% 2.95/0.99  
% 2.95/0.99  fof(f40,plain,(
% 2.95/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f26])).
% 2.95/0.99  
% 2.95/0.99  fof(f62,plain,(
% 2.95/0.99    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f46,plain,(
% 2.95/0.99    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f31])).
% 2.95/0.99  
% 2.95/0.99  fof(f61,plain,(
% 2.95/0.99    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f60,plain,(
% 2.95/0.99    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f2,axiom,(
% 2.95/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f41,plain,(
% 2.95/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f2])).
% 2.95/0.99  
% 2.95/0.99  cnf(c_9,plain,
% 2.95/0.99      ( ~ v1_relat_1(X0)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | v2_funct_1(X0)
% 2.95/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.95/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_24,negated_conjecture,
% 2.95/0.99      ( v1_funct_1(sK3) ),
% 2.95/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_385,plain,
% 2.95/0.99      ( ~ v1_relat_1(X0)
% 2.95/0.99      | v2_funct_1(X0)
% 2.95/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.95/0.99      | sK3 != X0 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_386,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3)
% 2.95/0.99      | v2_funct_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2687,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_22,negated_conjecture,
% 2.95/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.95/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_27,plain,
% 2.95/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_387,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_13,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2893,plain,
% 2.95/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.95/0.99      | v1_relat_1(sK3) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2894,plain,
% 2.95/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.95/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2893]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3580,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_2687,c_27,c_387,c_2894]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_16,plain,
% 2.95/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/0.99      | ~ r2_hidden(X3,X1)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | ~ v2_funct_1(X0)
% 2.95/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.95/0.99      | k1_xboole_0 = X2 ),
% 2.95/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_23,negated_conjecture,
% 2.95/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.95/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_330,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/0.99      | ~ r2_hidden(X3,X1)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | ~ v2_funct_1(X0)
% 2.95/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.95/0.99      | sK2 != X2
% 2.95/0.99      | sK2 != X1
% 2.95/0.99      | sK3 != X0
% 2.95/0.99      | k1_xboole_0 = X2 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_331,plain,
% 2.95/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.95/0.99      | ~ r2_hidden(X0,sK2)
% 2.95/0.99      | ~ v1_funct_1(sK3)
% 2.95/0.99      | ~ v2_funct_1(sK3)
% 2.95/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.95/0.99      | k1_xboole_0 = sK2 ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_335,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,sK2)
% 2.95/0.99      | ~ v2_funct_1(sK3)
% 2.95/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.95/0.99      | k1_xboole_0 = sK2 ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_331,c_24,c_22]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2088,plain,
% 2.95/0.99      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 2.95/0.99      inference(splitting,
% 2.95/0.99                [splitting(split),new_symbols(definition,[])],
% 2.95/0.99                [c_335]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2690,plain,
% 2.95/0.99      ( k1_xboole_0 = sK2
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top
% 2.95/0.99      | sP1_iProver_split = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3586,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sK2 = k1_xboole_0
% 2.95/0.99      | sP1_iProver_split = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3580,c_2690]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_20,negated_conjecture,
% 2.95/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.95/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2695,plain,
% 2.95/0.99      ( r2_hidden(sK4,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2087,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,sK2)
% 2.95/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.95/0.99      | ~ sP1_iProver_split ),
% 2.95/0.99      inference(splitting,
% 2.95/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.95/0.99                [c_335]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2691,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3286,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_2695,c_2691]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3587,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3580,c_3286]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_25,plain,
% 2.95/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_56,plain,
% 2.95/0.99      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.95/0.99      | v1_relat_1(X0) != iProver_top
% 2.95/0.99      | v1_funct_1(X0) != iProver_top
% 2.95/0.99      | v2_funct_1(X0) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_58,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v1_funct_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_56]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_8,plain,
% 2.95/0.99      ( ~ v1_relat_1(X0)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | v2_funct_1(X0)
% 2.95/0.99      | sK1(X0) != sK0(X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_59,plain,
% 2.95/0.99      ( sK1(X0) != sK0(X0)
% 2.95/0.99      | v1_relat_1(X0) != iProver_top
% 2.95/0.99      | v1_funct_1(X0) != iProver_top
% 2.95/0.99      | v2_funct_1(X0) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_61,plain,
% 2.95/0.99      ( sK1(sK3) != sK0(sK3)
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v1_funct_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_59]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_21,negated_conjecture,
% 2.95/0.99      ( ~ r2_hidden(X0,sK2)
% 2.95/0.99      | ~ r2_hidden(X1,sK2)
% 2.95/0.99      | v2_funct_1(sK3)
% 2.95/0.99      | X1 = X0
% 2.95/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2974,plain,
% 2.95/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.95/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 2.95/0.99      | v2_funct_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | sK1(sK3) = sK0(sK3) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2975,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.95/0.99      | sK1(sK3) = sK0(sK3)
% 2.95/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.95/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2974]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2693,plain,
% 2.95/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_15,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2699,plain,
% 2.95/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.95/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3693,plain,
% 2.95/0.99      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_2693,c_2699]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_14,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.95/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2700,plain,
% 2.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.95/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3938,plain,
% 2.95/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.95/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3693,c_2700]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4101,plain,
% 2.95/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3938,c_27]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_6,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.95/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2703,plain,
% 2.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.95/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4106,plain,
% 2.95/0.99      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_4101,c_2703]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_11,plain,
% 2.95/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.95/0.99      | ~ v1_relat_1(X0)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | v2_funct_1(X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_359,plain,
% 2.95/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.95/0.99      | ~ v1_relat_1(X0)
% 2.95/0.99      | v2_funct_1(X0)
% 2.95/0.99      | sK3 != X0 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_360,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ v1_relat_1(sK3)
% 2.95/0.99      | v2_funct_1(sK3) ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2689,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_361,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3488,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_2689,c_27,c_361,c_2894]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4,plain,
% 2.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.95/0.99      | ~ r2_hidden(X2,X0)
% 2.95/0.99      | r2_hidden(X2,X1) ),
% 2.95/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5,plain,
% 2.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.95/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_192,plain,
% 2.95/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.95/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_193,plain,
% 2.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.95/0.99      inference(renaming,[status(thm)],[c_192]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_243,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.95/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_193]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2692,plain,
% 2.95/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.95/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.95/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4299,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 2.95/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3488,c_2692]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4866,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_4106,c_4299]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_10,plain,
% 2.95/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.95/0.99      | ~ v1_relat_1(X0)
% 2.95/0.99      | ~ v1_funct_1(X0)
% 2.95/0.99      | v2_funct_1(X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_372,plain,
% 2.95/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.95/0.99      | ~ v1_relat_1(X0)
% 2.95/0.99      | v2_funct_1(X0)
% 2.95/0.99      | sK3 != X0 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_373,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ v1_relat_1(sK3)
% 2.95/0.99      | v2_funct_1(sK3) ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_372]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2688,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_374,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3481,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_2688,c_27,c_374,c_2894]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4300,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),X0) = iProver_top
% 2.95/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3481,c_2692]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4877,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_4106,c_4300]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4948,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_3587,c_25,c_27,c_58,c_61,c_2894,c_2975,c_3286,c_4866,c_4877]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4954,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sK2 = k1_xboole_0 ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3586,c_4948]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f64]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_76,plain,
% 2.95/0.99      ( r1_tarski(sK3,sK3) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_0,plain,
% 2.95/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.95/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_80,plain,
% 2.95/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_398,plain,
% 2.95/0.99      ( ~ v1_relat_1(X0) | v2_funct_1(X0) | sK1(X0) != sK0(X0) | sK3 != X0 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_399,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_17,negated_conjecture,
% 2.95/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.95/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_639,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_399,c_17]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_730,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sK5 != sK4 ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_386,c_17]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_821,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_373,c_17]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_912,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_360,c_17]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2098,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2110,plain,
% 2.95/0.99      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_2098]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_12,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.95/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.95/0.99      | ~ v1_relat_1(X1)
% 2.95/0.99      | ~ v1_funct_1(X1)
% 2.95/0.99      | ~ v2_funct_1(X1)
% 2.95/0.99      | X0 = X2
% 2.95/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.95/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_411,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.95/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.95/0.99      | ~ v1_relat_1(X1)
% 2.95/0.99      | ~ v2_funct_1(X1)
% 2.95/0.99      | X2 = X0
% 2.95/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.95/0.99      | sK3 != X1 ),
% 2.95/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_412,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.95/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.95/0.99      | ~ v1_relat_1(sK3)
% 2.95/0.99      | ~ v2_funct_1(sK3)
% 2.95/0.99      | X0 = X1
% 2.95/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.95/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2086,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 2.95/0.99      inference(splitting,
% 2.95/0.99                [splitting(split),new_symbols(definition,[])],
% 2.95/0.99                [c_412]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2091,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2977,plain,
% 2.95/0.99      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_2091]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3085,plain,
% 2.95/0.99      ( sK1(sK3) != sK1(sK3) | sK1(sK3) = sK0(sK3) | sK0(sK3) != sK1(sK3) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_2977]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2085,plain,
% 2.95/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.95/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.95/0.99      | X0 = X1
% 2.95/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.95/0.99      | ~ sP0_iProver_split ),
% 2.95/0.99      inference(splitting,
% 2.95/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.95/0.99                [c_412]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3815,plain,
% 2.95/0.99      ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
% 2.95/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ sP0_iProver_split
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 2.95/0.99      | sK0(sK3) = sK1(X0) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_2085]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3817,plain,
% 2.95/0.99      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ sP0_iProver_split
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sK0(sK3) = sK1(sK3) ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_3815]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_18,negated_conjecture,
% 2.95/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.95/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2697,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3590,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3580,c_2697]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2694,plain,
% 2.95/0.99      ( X0 = X1
% 2.95/0.99      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.95/0.99      | r2_hidden(X1,sK2) != iProver_top
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3945,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | sK1(sK3) = X0
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3590,c_2694]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_627,plain,
% 2.95/0.99      ( ~ v1_relat_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | sK1(sK3) != sK0(sK3) ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_399,c_18]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_809,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ v1_relat_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_373,c_18]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_810,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_900,plain,
% 2.95/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.95/0.99      | ~ v1_relat_1(sK3)
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.95/0.99      inference(resolution,[status(thm)],[c_360,c_18]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_901,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.95/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2684,plain,
% 2.95/0.99      ( v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top
% 2.95/0.99      | sP0_iProver_split = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2086]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2118,plain,
% 2.95/0.99      ( v1_relat_1(sK3) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top
% 2.95/0.99      | sP0_iProver_split = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2086]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2928,plain,
% 2.95/0.99      ( v2_funct_1(sK3) != iProver_top | sP0_iProver_split = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_2684,c_27,c_2118,c_2894]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3816,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 2.95/0.99      | sK0(sK3) = sK1(X0)
% 2.95/0.99      | r2_hidden(sK1(X0),k1_relat_1(sK3)) != iProver_top
% 2.95/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.95/0.99      | sP0_iProver_split != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3815]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3818,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sK0(sK3) = sK1(sK3)
% 2.95/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.95/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.95/0.99      | sP0_iProver_split != iProver_top ),
% 2.95/0.99      inference(instantiation,[status(thm)],[c_3816]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4062,plain,
% 2.95/0.99      ( r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | sK1(sK3) = X0
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0) ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_3945,c_22,c_27,c_76,c_80,c_627,c_810,c_901,c_2110,c_2893,
% 2.95/0.99                 c_2894,c_2928,c_3085,c_3590,c_3818]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4063,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0)
% 2.95/0.99      | k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | sK1(sK3) = X0
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top ),
% 2.95/0.99      inference(renaming,[status(thm)],[c_4062]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4074,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4)
% 2.95/0.99      | sK1(sK3) = sK0(sK3)
% 2.95/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.95/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top ),
% 2.95/0.99      inference(equality_resolution,[status(thm)],[c_4063]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5110,plain,
% 2.95/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_4074,c_25,c_22,c_27,c_58,c_61,c_76,c_80,c_627,c_810,
% 2.95/0.99                 c_901,c_2110,c_2118,c_2893,c_2894,c_2975,c_3085,c_3590,
% 2.95/0.99                 c_3818,c_4866,c_4877]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5131,plain,
% 2.95/0.99      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.95/0.99      | sK5 = X0
% 2.95/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.95/0.99      | r2_hidden(sK5,sK2) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_5110,c_2694]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5159,plain,
% 2.95/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_5131,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5161,plain,
% 2.95/0.99      ( v2_funct_1(sK3) ),
% 2.95/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5159]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5164,plain,
% 2.95/0.99      ( sK2 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_5159,c_2690]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5295,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.95/0.99      | sK2 = k1_xboole_0 ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_5164,c_4948]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_19,negated_conjecture,
% 2.95/0.99      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.95/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_2696,plain,
% 2.95/0.99      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3285,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_2696,c_2691]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3588,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.95/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_3580,c_3285]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4956,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_3588,c_25,c_27,c_58,c_61,c_2894,c_2975,c_3285,c_4866,c_4877]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5113,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.95/0.99      | sP1_iProver_split != iProver_top ),
% 2.95/0.99      inference(demodulation,[status(thm)],[c_5110,c_4956]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5417,plain,
% 2.95/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.95/0.99      | sK2 = k1_xboole_0 ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_5164,c_5113]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5876,plain,
% 2.95/0.99      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_5295,c_5417]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5878,plain,
% 2.95/0.99      ( sK2 = k1_xboole_0 ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_4954,c_22,c_76,c_80,c_639,c_730,c_821,c_912,c_2110,c_2086,
% 2.95/0.99                 c_2893,c_3085,c_3817,c_5161,c_5876]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5895,plain,
% 2.95/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(demodulation,[status(thm)],[c_5878,c_2696]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_6066,plain,
% 2.95/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 2.95/0.99      inference(global_propositional_subsumption,
% 2.95/0.99                [status(thm)],
% 2.95/0.99                [c_5895,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_6071,plain,
% 2.95/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 2.95/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_6066,c_2692]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_3,plain,
% 2.95/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.95/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_72,plain,
% 2.95/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_4297,plain,
% 2.95/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 2.95/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(superposition,[status(thm)],[c_2696,c_2692]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_5885,plain,
% 2.95/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 2.95/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.95/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.95/0.99      inference(demodulation,[status(thm)],[c_5878,c_4297]) ).
% 2.95/0.99  
% 2.95/0.99  cnf(c_6587,plain,
% 2.95/0.99      ( r2_hidden(sK5,X0) = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_6071,c_25,c_27,c_58,c_61,c_72,c_2894,c_2975,c_4866,c_4877,
% 2.95/1.00                 c_5885]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2685,plain,
% 2.95/1.00      ( X0 = X1
% 2.95/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.95/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | sP0_iProver_split != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2085]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5130,plain,
% 2.95/1.00      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.95/1.00      | sK5 = X0
% 2.95/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | sP0_iProver_split != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_5110,c_2685]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5192,plain,
% 2.95/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | sK5 = X0
% 2.95/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_5130,c_25,c_27,c_58,c_61,c_2118,c_2894,c_2975,c_4866,c_4877]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5193,plain,
% 2.95/1.00      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.95/1.00      | sK5 = X0
% 2.95/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_5192]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5204,plain,
% 2.95/1.00      ( sK5 = sK4
% 2.95/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.95/1.00      inference(equality_resolution,[status(thm)],[c_5193]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5778,plain,
% 2.95/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.95/1.00      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_5204,c_25,c_27,c_33,c_34,c_58,c_61,c_2118,c_2894,c_2975,
% 2.95/1.00                 c_3773,c_4866,c_4877]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6595,plain,
% 2.95/1.00      ( r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_6587,c_5778]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5896,plain,
% 2.95/1.00      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 2.95/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_5878,c_2695]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6186,plain,
% 2.95/1.00      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_5896,c_25,c_27,c_58,c_61,c_2894,c_2975,c_4866,c_4877]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6191,plain,
% 2.95/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 2.95/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_6186,c_2692]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_4298,plain,
% 2.95/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 2.95/1.00      | r1_tarski(sK2,X0) != iProver_top
% 2.95/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_2695,c_2692]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_5884,plain,
% 2.95/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 2.95/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.95/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_5878,c_4298]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6609,plain,
% 2.95/1.00      ( r2_hidden(sK4,X0) = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_6191,c_25,c_27,c_58,c_61,c_72,c_2894,c_2975,c_4866,c_4877,
% 2.95/1.00                 c_5884]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_7065,plain,
% 2.95/1.00      ( $false ),
% 2.95/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6595,c_6609]) ).
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  ------                               Statistics
% 2.95/1.00  
% 2.95/1.00  ------ General
% 2.95/1.00  
% 2.95/1.00  abstr_ref_over_cycles:                  0
% 2.95/1.00  abstr_ref_under_cycles:                 0
% 2.95/1.00  gc_basic_clause_elim:                   0
% 2.95/1.00  forced_gc_time:                         0
% 2.95/1.00  parsing_time:                           0.009
% 2.95/1.00  unif_index_cands_time:                  0.
% 2.95/1.00  unif_index_add_time:                    0.
% 2.95/1.00  orderings_time:                         0.
% 2.95/1.00  out_proof_time:                         0.014
% 2.95/1.00  total_time:                             0.209
% 2.95/1.00  num_of_symbols:                         53
% 2.95/1.00  num_of_terms:                           3998
% 2.95/1.00  
% 2.95/1.00  ------ Preprocessing
% 2.95/1.00  
% 2.95/1.00  num_of_splits:                          2
% 2.95/1.00  num_of_split_atoms:                     2
% 2.95/1.00  num_of_reused_defs:                     0
% 2.95/1.00  num_eq_ax_congr_red:                    17
% 2.95/1.00  num_of_sem_filtered_clauses:            1
% 2.95/1.00  num_of_subtypes:                        0
% 2.95/1.00  monotx_restored_types:                  0
% 2.95/1.00  sat_num_of_epr_types:                   0
% 2.95/1.00  sat_num_of_non_cyclic_types:            0
% 2.95/1.00  sat_guarded_non_collapsed_types:        0
% 2.95/1.00  num_pure_diseq_elim:                    0
% 2.95/1.00  simp_replaced_by:                       0
% 2.95/1.00  res_preprocessed:                       123
% 2.95/1.00  prep_upred:                             0
% 2.95/1.00  prep_unflattend:                        18
% 2.95/1.00  smt_new_axioms:                         0
% 2.95/1.00  pred_elim_cands:                        5
% 2.95/1.00  pred_elim:                              2
% 2.95/1.00  pred_elim_cl:                           2
% 2.95/1.00  pred_elim_cycles:                       6
% 2.95/1.00  merged_defs:                            8
% 2.95/1.00  merged_defs_ncl:                        0
% 2.95/1.00  bin_hyper_res:                          9
% 2.95/1.00  prep_cycles:                            4
% 2.95/1.00  pred_elim_time:                         0.025
% 2.95/1.00  splitting_time:                         0.
% 2.95/1.00  sem_filter_time:                        0.
% 2.95/1.00  monotx_time:                            0.
% 2.95/1.00  subtype_inf_time:                       0.
% 2.95/1.00  
% 2.95/1.00  ------ Problem properties
% 2.95/1.00  
% 2.95/1.00  clauses:                                24
% 2.95/1.00  conjectures:                            6
% 2.95/1.00  epr:                                    9
% 2.95/1.00  horn:                                   19
% 2.95/1.00  ground:                                 11
% 2.95/1.00  unary:                                  3
% 2.95/1.00  binary:                                 9
% 2.95/1.00  lits:                                   61
% 2.95/1.00  lits_eq:                                12
% 2.95/1.00  fd_pure:                                0
% 2.95/1.00  fd_pseudo:                              0
% 2.95/1.00  fd_cond:                                0
% 2.95/1.00  fd_pseudo_cond:                         3
% 2.95/1.00  ac_symbols:                             0
% 2.95/1.00  
% 2.95/1.00  ------ Propositional Solver
% 2.95/1.00  
% 2.95/1.00  prop_solver_calls:                      30
% 2.95/1.00  prop_fast_solver_calls:                 1202
% 2.95/1.00  smt_solver_calls:                       0
% 2.95/1.00  smt_fast_solver_calls:                  0
% 2.95/1.00  prop_num_of_clauses:                    2021
% 2.95/1.00  prop_preprocess_simplified:             5922
% 2.95/1.00  prop_fo_subsumed:                       34
% 2.95/1.00  prop_solver_time:                       0.
% 2.95/1.00  smt_solver_time:                        0.
% 2.95/1.00  smt_fast_solver_time:                   0.
% 2.95/1.00  prop_fast_solver_time:                  0.
% 2.95/1.00  prop_unsat_core_time:                   0.
% 2.95/1.00  
% 2.95/1.00  ------ QBF
% 2.95/1.00  
% 2.95/1.00  qbf_q_res:                              0
% 2.95/1.00  qbf_num_tautologies:                    0
% 2.95/1.00  qbf_prep_cycles:                        0
% 2.95/1.00  
% 2.95/1.00  ------ BMC1
% 2.95/1.00  
% 2.95/1.00  bmc1_current_bound:                     -1
% 2.95/1.00  bmc1_last_solved_bound:                 -1
% 2.95/1.00  bmc1_unsat_core_size:                   -1
% 2.95/1.00  bmc1_unsat_core_parents_size:           -1
% 2.95/1.00  bmc1_merge_next_fun:                    0
% 2.95/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.95/1.00  
% 2.95/1.00  ------ Instantiation
% 2.95/1.00  
% 2.95/1.00  inst_num_of_clauses:                    593
% 2.95/1.00  inst_num_in_passive:                    149
% 2.95/1.00  inst_num_in_active:                     406
% 2.95/1.00  inst_num_in_unprocessed:                38
% 2.95/1.00  inst_num_of_loops:                      430
% 2.95/1.00  inst_num_of_learning_restarts:          0
% 2.95/1.00  inst_num_moves_active_passive:          19
% 2.95/1.00  inst_lit_activity:                      0
% 2.95/1.00  inst_lit_activity_moves:                0
% 2.95/1.00  inst_num_tautologies:                   0
% 2.95/1.00  inst_num_prop_implied:                  0
% 2.95/1.00  inst_num_existing_simplified:           0
% 2.95/1.00  inst_num_eq_res_simplified:             0
% 2.95/1.00  inst_num_child_elim:                    0
% 2.95/1.00  inst_num_of_dismatching_blockings:      223
% 2.95/1.00  inst_num_of_non_proper_insts:           911
% 2.95/1.00  inst_num_of_duplicates:                 0
% 2.95/1.00  inst_inst_num_from_inst_to_res:         0
% 2.95/1.00  inst_dismatching_checking_time:         0.
% 2.95/1.00  
% 2.95/1.00  ------ Resolution
% 2.95/1.00  
% 2.95/1.00  res_num_of_clauses:                     0
% 2.95/1.00  res_num_in_passive:                     0
% 2.95/1.00  res_num_in_active:                      0
% 2.95/1.00  res_num_of_loops:                       127
% 2.95/1.00  res_forward_subset_subsumed:            97
% 2.95/1.00  res_backward_subset_subsumed:           0
% 2.95/1.00  res_forward_subsumed:                   0
% 2.95/1.00  res_backward_subsumed:                  0
% 2.95/1.00  res_forward_subsumption_resolution:     0
% 2.95/1.00  res_backward_subsumption_resolution:    0
% 2.95/1.00  res_clause_to_clause_subsumption:       245
% 2.95/1.00  res_orphan_elimination:                 0
% 2.95/1.00  res_tautology_del:                      91
% 2.95/1.00  res_num_eq_res_simplified:              0
% 2.95/1.00  res_num_sel_changes:                    0
% 2.95/1.00  res_moves_from_active_to_pass:          0
% 2.95/1.00  
% 2.95/1.00  ------ Superposition
% 2.95/1.00  
% 2.95/1.00  sup_time_total:                         0.
% 2.95/1.00  sup_time_generating:                    0.
% 2.95/1.00  sup_time_sim_full:                      0.
% 2.95/1.00  sup_time_sim_immed:                     0.
% 2.95/1.00  
% 2.95/1.00  sup_num_of_clauses:                     103
% 2.95/1.00  sup_num_in_active:                      62
% 2.95/1.00  sup_num_in_passive:                     41
% 2.95/1.00  sup_num_of_loops:                       85
% 2.95/1.00  sup_fw_superposition:                   68
% 2.95/1.00  sup_bw_superposition:                   74
% 2.95/1.00  sup_immediate_simplified:               27
% 2.95/1.00  sup_given_eliminated:                   1
% 2.95/1.00  comparisons_done:                       0
% 2.95/1.00  comparisons_avoided:                    12
% 2.95/1.00  
% 2.95/1.00  ------ Simplifications
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  sim_fw_subset_subsumed:                 16
% 2.95/1.00  sim_bw_subset_subsumed:                 5
% 2.95/1.00  sim_fw_subsumed:                        0
% 2.95/1.00  sim_bw_subsumed:                        2
% 2.95/1.00  sim_fw_subsumption_res:                 1
% 2.95/1.00  sim_bw_subsumption_res:                 0
% 2.95/1.00  sim_tautology_del:                      1
% 2.95/1.00  sim_eq_tautology_del:                   11
% 2.95/1.00  sim_eq_res_simp:                        0
% 2.95/1.00  sim_fw_demodulated:                     0
% 2.95/1.00  sim_bw_demodulated:                     30
% 2.95/1.00  sim_light_normalised:                   2
% 2.95/1.00  sim_joinable_taut:                      0
% 2.95/1.00  sim_joinable_simp:                      0
% 2.95/1.00  sim_ac_normalised:                      0
% 2.95/1.00  sim_smt_subsumption:                    0
% 2.95/1.00  
%------------------------------------------------------------------------------
