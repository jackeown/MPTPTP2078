%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:54 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_30)

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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_317,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_318,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_2350,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_47,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_49,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_50,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_52,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_53,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_55,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_56,plain,
    ( sK1(X0) != sK0(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_58,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2545,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2546,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2615,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2616,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2615])).

cnf(c_2356,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2362,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2712,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2356,c_2362])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2935,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_2363])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2585,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK3),X0)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3078,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | r2_hidden(sK0(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_3081,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_2600,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
    | r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3076,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | r2_hidden(sK1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2600])).

cnf(c_3085,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3076])).

cnf(c_3233,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2350,c_22,c_24,c_49,c_52,c_55,c_58,c_2546,c_2616,c_2935,c_3081,c_3085])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_263,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_21,c_19])).

cnf(c_1955,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_267])).

cnf(c_2353,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_3238,plain,
    ( sK2 = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_2353])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2359,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1954,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_267])).

cnf(c_2354,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_2941,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_2354])).

cnf(c_3240,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_2941])).

cnf(c_15,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2360,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3242,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3233,c_2360])).

cnf(c_3247,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3240,c_3242])).

cnf(c_3800,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3238,c_3247])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2358,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2942,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_2354])).

cnf(c_3239,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_2942])).

cnf(c_3801,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3238,c_3239])).

cnf(c_4124,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_3800,c_3801])).

cnf(c_330,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_331,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_571,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_331,c_14])).

cnf(c_662,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_318,c_14])).

cnf(c_304,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_305,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_753,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_305,c_14])).

cnf(c_291,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_292,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_844,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_292,c_14])).

cnf(c_1964,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_1975,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_1957,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1982,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_1953,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_344])).

cnf(c_1958,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2618,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2723,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_1952,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_344])).

cnf(c_3225,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_3235,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3233])).

cnf(c_4126,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_19,c_571,c_662,c_753,c_844,c_1975,c_1982,c_1953,c_2545,c_2723,c_3225,c_3235])).

cnf(c_4136,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4126,c_2712])).

cnf(c_4140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4126,c_2356])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_2355,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_3599,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2363,c_2355])).

cnf(c_4251,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4140,c_3599])).

cnf(c_4869,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4136,c_4251])).

cnf(c_2348,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1952])).

cnf(c_3444,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3242,c_2348])).

cnf(c_1983,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_3762,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sK5 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_22,c_24,c_49,c_52,c_55,c_58,c_1983,c_2546,c_2616,c_2935,c_3081,c_3085])).

cnf(c_3763,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3762])).

cnf(c_3773,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3763])).

cnf(c_3831,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_22,c_24,c_30,c_31,c_49,c_52,c_55,c_58,c_1983,c_2546,c_2616,c_2935,c_3081,c_3085,c_3177])).

cnf(c_4871,plain,
    ( r2_hidden(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4869,c_3831])).

cnf(c_4139,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4126,c_2358])).

cnf(c_4138,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4126,c_2359])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4871,c_4139,c_4138,c_3233])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:13:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.69/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.00  
% 2.69/1.00  ------  iProver source info
% 2.69/1.00  
% 2.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.00  git: non_committed_changes: false
% 2.69/1.00  git: last_make_outside_of_git: false
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     num_symb
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       true
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  ------ Parsing...
% 2.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.00  ------ Proving...
% 2.69/1.00  ------ Problem Properties 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  clauses                                 21
% 2.69/1.00  conjectures                             6
% 2.69/1.00  EPR                                     5
% 2.69/1.00  Horn                                    16
% 2.69/1.00  unary                                   2
% 2.69/1.00  binary                                  8
% 2.69/1.00  lits                                    55
% 2.69/1.00  lits eq                                 12
% 2.69/1.00  fd_pure                                 0
% 2.69/1.00  fd_pseudo                               0
% 2.69/1.00  fd_cond                                 1
% 2.69/1.00  fd_pseudo_cond                          2
% 2.69/1.00  AC symbols                              0
% 2.69/1.00  
% 2.69/1.00  ------ Schedule dynamic 5 is on 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  Current options:
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     none
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       false
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ Proving...
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS status Theorem for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  fof(f6,axiom,(
% 2.69/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f19,plain,(
% 2.69/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.69/1.00    inference(ennf_transformation,[],[f6])).
% 2.69/1.00  
% 2.69/1.00  fof(f20,plain,(
% 2.69/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(flattening,[],[f19])).
% 2.69/1.00  
% 2.69/1.00  fof(f28,plain,(
% 2.69/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(nnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f29,plain,(
% 2.69/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(rectify,[],[f28])).
% 2.69/1.00  
% 2.69/1.00  fof(f30,plain,(
% 2.69/1.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f31,plain,(
% 2.69/1.00    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 2.69/1.00  
% 2.69/1.00  fof(f46,plain,(
% 2.69/1.00    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f11,conjecture,(
% 2.69/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f12,negated_conjecture,(
% 2.69/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.69/1.00    inference(negated_conjecture,[],[f11])).
% 2.69/1.00  
% 2.69/1.00  fof(f26,plain,(
% 2.69/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.69/1.00    inference(ennf_transformation,[],[f12])).
% 2.69/1.00  
% 2.69/1.00  fof(f27,plain,(
% 2.69/1.00    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.69/1.00    inference(flattening,[],[f26])).
% 2.69/1.00  
% 2.69/1.00  fof(f32,plain,(
% 2.69/1.00    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.69/1.00    inference(nnf_transformation,[],[f27])).
% 2.69/1.00  
% 2.69/1.00  fof(f33,plain,(
% 2.69/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.69/1.00    inference(flattening,[],[f32])).
% 2.69/1.00  
% 2.69/1.00  fof(f34,plain,(
% 2.69/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.69/1.00    inference(rectify,[],[f33])).
% 2.69/1.00  
% 2.69/1.00  fof(f36,plain,(
% 2.69/1.00    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f35,plain,(
% 2.69/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f37,plain,(
% 2.69/1.00    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f36,f35])).
% 2.69/1.00  
% 2.69/1.00  fof(f52,plain,(
% 2.69/1.00    v1_funct_1(sK3)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f54,plain,(
% 2.69/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f44,plain,(
% 2.69/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f45,plain,(
% 2.69/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f47,plain,(
% 2.69/1.00    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f7,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f21,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f7])).
% 2.69/1.00  
% 2.69/1.00  fof(f48,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f21])).
% 2.69/1.00  
% 2.69/1.00  fof(f55,plain,(
% 2.69/1.00    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f9,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f23,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f9])).
% 2.69/1.00  
% 2.69/1.00  fof(f50,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f23])).
% 2.69/1.00  
% 2.69/1.00  fof(f8,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f22,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.00    inference(ennf_transformation,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f49,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f2,axiom,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f15,plain,(
% 2.69/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.69/1.00    inference(ennf_transformation,[],[f2])).
% 2.69/1.00  
% 2.69/1.00  fof(f39,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f15])).
% 2.69/1.00  
% 2.69/1.00  fof(f10,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f24,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.69/1.00    inference(ennf_transformation,[],[f10])).
% 2.69/1.00  
% 2.69/1.00  fof(f25,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.69/1.00    inference(flattening,[],[f24])).
% 2.69/1.00  
% 2.69/1.00  fof(f51,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f25])).
% 2.69/1.00  
% 2.69/1.00  fof(f53,plain,(
% 2.69/1.00    v1_funct_2(sK3,sK2,sK2)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f57,plain,(
% 2.69/1.00    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f58,plain,(
% 2.69/1.00    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f56,plain,(
% 2.69/1.00    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f59,plain,(
% 2.69/1.00    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.69/1.00    inference(cnf_transformation,[],[f37])).
% 2.69/1.00  
% 2.69/1.00  fof(f43,plain,(
% 2.69/1.00    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f31])).
% 2.69/1.00  
% 2.69/1.00  fof(f1,axiom,(
% 2.69/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f14,plain,(
% 2.69/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.69/1.00    inference(ennf_transformation,[],[f1])).
% 2.69/1.00  
% 2.69/1.00  fof(f38,plain,(
% 2.69/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f14])).
% 2.69/1.00  
% 2.69/1.00  fof(f4,axiom,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f13,plain,(
% 2.69/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.69/1.00    inference(unused_predicate_definition_removal,[],[f4])).
% 2.69/1.00  
% 2.69/1.00  fof(f16,plain,(
% 2.69/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.69/1.00    inference(ennf_transformation,[],[f13])).
% 2.69/1.00  
% 2.69/1.00  fof(f41,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f16])).
% 2.69/1.00  
% 2.69/1.00  cnf(c_6,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_21,negated_conjecture,
% 2.69/1.00      ( v1_funct_1(sK3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_317,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.69/1.00      | sK3 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_318,plain,
% 2.69/1.00      ( ~ v1_relat_1(sK3)
% 2.69/1.00      | v2_funct_1(sK3)
% 2.69/1.00      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2350,plain,
% 2.69/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.69/1.00      | v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_22,plain,
% 2.69/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_19,negated_conjecture,
% 2.69/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.69/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_24,plain,
% 2.69/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_8,plain,
% 2.69/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | v2_funct_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_47,plain,
% 2.69/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 2.69/1.00      | v1_relat_1(X0) != iProver_top
% 2.69/1.00      | v1_funct_1(X0) != iProver_top
% 2.69/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_49,plain,
% 2.69/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.69/1.00      | v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v1_funct_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_47]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7,plain,
% 2.69/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | v2_funct_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_50,plain,
% 2.69/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 2.69/1.00      | v1_relat_1(X0) != iProver_top
% 2.69/1.00      | v1_funct_1(X0) != iProver_top
% 2.69/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_52,plain,
% 2.69/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.69/1.00      | v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v1_funct_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_50]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_53,plain,
% 2.69/1.00      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.69/1.00      | v1_relat_1(X0) != iProver_top
% 2.69/1.00      | v1_funct_1(X0) != iProver_top
% 2.69/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_55,plain,
% 2.69/1.00      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.69/1.00      | v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v1_funct_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_53]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_5,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | sK1(X0) != sK0(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_56,plain,
% 2.69/1.00      ( sK1(X0) != sK0(X0)
% 2.69/1.00      | v1_relat_1(X0) != iProver_top
% 2.69/1.00      | v1_funct_1(X0) != iProver_top
% 2.69/1.00      | v2_funct_1(X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_58,plain,
% 2.69/1.00      ( sK1(sK3) != sK0(sK3)
% 2.69/1.00      | v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v1_funct_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_56]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_10,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | v1_relat_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2545,plain,
% 2.69/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.69/1.00      | v1_relat_1(sK3) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2546,plain,
% 2.69/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.69/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_2545]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_18,negated_conjecture,
% 2.69/1.00      ( ~ r2_hidden(X0,sK2)
% 2.69/1.00      | ~ r2_hidden(X1,sK2)
% 2.69/1.00      | v2_funct_1(sK3)
% 2.69/1.00      | X1 = X0
% 2.69/1.00      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2615,plain,
% 2.69/1.00      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.69/1.00      | ~ r2_hidden(sK0(sK3),sK2)
% 2.69/1.00      | v2_funct_1(sK3)
% 2.69/1.00      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.69/1.00      | sK1(sK3) = sK0(sK3) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2616,plain,
% 2.69/1.00      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.69/1.00      | sK1(sK3) = sK0(sK3)
% 2.69/1.00      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.69/1.00      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_2615]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2356,plain,
% 2.69/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_12,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2362,plain,
% 2.69/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.69/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2712,plain,
% 2.69/1.00      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2356,c_2362]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_11,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2363,plain,
% 2.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2935,plain,
% 2.69/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.69/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2712,c_2363]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | ~ r2_hidden(X2,X0)
% 2.69/1.00      | r2_hidden(X2,X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2585,plain,
% 2.69/1.00      ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
% 2.69/1.00      | r2_hidden(sK0(sK3),X0)
% 2.69/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3078,plain,
% 2.69/1.00      ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
% 2.69/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.69/1.00      | r2_hidden(sK0(sK3),sK2) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2585]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3081,plain,
% 2.69/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) != iProver_top
% 2.69/1.00      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK0(sK3),sK2) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2600,plain,
% 2.69/1.00      ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
% 2.69/1.00      | r2_hidden(sK1(sK3),X0)
% 2.69/1.00      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3076,plain,
% 2.69/1.00      ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
% 2.69/1.00      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.69/1.00      | r2_hidden(sK1(sK3),sK2) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2600]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3085,plain,
% 2.69/1.00      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) != iProver_top
% 2.69/1.00      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK1(sK3),sK2) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3076]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3233,plain,
% 2.69/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_2350,c_22,c_24,c_49,c_52,c_55,c_58,c_2546,c_2616,
% 2.69/1.00                 c_2935,c_3081,c_3085]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_13,plain,
% 2.69/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | ~ r2_hidden(X3,X1)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | ~ v2_funct_1(X0)
% 2.69/1.00      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.69/1.00      | k1_xboole_0 = X2 ),
% 2.69/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_20,negated_conjecture,
% 2.69/1.00      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.69/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_262,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.00      | ~ r2_hidden(X3,X1)
% 2.69/1.00      | ~ v1_funct_1(X0)
% 2.69/1.00      | ~ v2_funct_1(X0)
% 2.69/1.00      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.69/1.00      | sK2 != X2
% 2.69/1.00      | sK2 != X1
% 2.69/1.00      | sK3 != X0
% 2.69/1.00      | k1_xboole_0 = X2 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_263,plain,
% 2.69/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.69/1.00      | ~ r2_hidden(X0,sK2)
% 2.69/1.00      | ~ v1_funct_1(sK3)
% 2.69/1.00      | ~ v2_funct_1(sK3)
% 2.69/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.69/1.00      | k1_xboole_0 = sK2 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_262]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_267,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,sK2)
% 2.69/1.00      | ~ v2_funct_1(sK3)
% 2.69/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.69/1.00      | k1_xboole_0 = sK2 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_263,c_21,c_19]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1955,plain,
% 2.69/1.00      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k1_xboole_0 = sK2 ),
% 2.69/1.00      inference(splitting,
% 2.69/1.00                [splitting(split),new_symbols(definition,[])],
% 2.69/1.00                [c_267]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2353,plain,
% 2.69/1.00      ( k1_xboole_0 = sK2
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top
% 2.69/1.00      | sP1_iProver_split = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3238,plain,
% 2.69/1.00      ( sK2 = k1_xboole_0 | sP1_iProver_split = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3233,c_2353]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_16,negated_conjecture,
% 2.69/1.00      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2359,plain,
% 2.69/1.00      ( r2_hidden(sK5,sK2) = iProver_top
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1954,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,sK2)
% 2.69/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.69/1.00      | ~ sP1_iProver_split ),
% 2.69/1.00      inference(splitting,
% 2.69/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.69/1.00                [c_267]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2354,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.69/1.00      | r2_hidden(X0,sK2) != iProver_top
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1954]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2941,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2359,c_2354]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3240,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3233,c_2941]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_15,negated_conjecture,
% 2.69/1.00      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.69/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2360,plain,
% 2.69/1.00      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3242,plain,
% 2.69/1.00      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3233,c_2360]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3247,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_3240,c_3242]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3800,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.69/1.00      | sK2 = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3238,c_3247]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_17,negated_conjecture,
% 2.69/1.00      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.69/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2358,plain,
% 2.69/1.00      ( r2_hidden(sK4,sK2) = iProver_top
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2942,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2358,c_2354]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3239,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.69/1.00      | sP1_iProver_split != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3233,c_2942]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3801,plain,
% 2.69/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.69/1.00      | sK2 = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3238,c_3239]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4124,plain,
% 2.69/1.00      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3800,c_3801]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_330,plain,
% 2.69/1.00      ( ~ v1_relat_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | sK1(X0) != sK0(X0)
% 2.69/1.00      | sK3 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_331,plain,
% 2.69/1.00      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_330]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_14,negated_conjecture,
% 2.69/1.00      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.69/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_571,plain,
% 2.69/1.00      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_331,c_14]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_662,plain,
% 2.69/1.00      ( ~ v1_relat_1(sK3)
% 2.69/1.00      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.69/1.00      | sK5 != sK4 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_318,c_14]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_304,plain,
% 2.69/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | sK3 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_305,plain,
% 2.69/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ v1_relat_1(sK3)
% 2.69/1.00      | v2_funct_1(sK3) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_304]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_753,plain,
% 2.69/1.00      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ v1_relat_1(sK3)
% 2.69/1.00      | sK5 != sK4 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_305,c_14]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_291,plain,
% 2.69/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | v2_funct_1(X0)
% 2.69/1.00      | sK3 != X0 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_292,plain,
% 2.69/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ v1_relat_1(sK3)
% 2.69/1.00      | v2_funct_1(sK3) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_291]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_844,plain,
% 2.69/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ v1_relat_1(sK3)
% 2.69/1.00      | sK5 != sK4 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_292,c_14]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1964,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1975,plain,
% 2.69/1.00      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1964]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1957,plain,( X0 = X0 ),theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1982,plain,
% 2.69/1.00      ( sK3 = sK3 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1957]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_9,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.69/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.69/1.00      | ~ v1_relat_1(X1)
% 2.69/1.00      | ~ v1_funct_1(X1)
% 2.69/1.00      | ~ v2_funct_1(X1)
% 2.69/1.00      | X0 = X2
% 2.69/1.00      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.69/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_343,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.69/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.69/1.00      | ~ v1_relat_1(X1)
% 2.69/1.00      | ~ v2_funct_1(X1)
% 2.69/1.00      | X2 = X0
% 2.69/1.00      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.69/1.00      | sK3 != X1 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_344,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.69/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.69/1.00      | ~ v1_relat_1(sK3)
% 2.69/1.00      | ~ v2_funct_1(sK3)
% 2.69/1.00      | X0 = X1
% 2.69/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_343]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1953,plain,
% 2.69/1.00      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 2.69/1.00      inference(splitting,
% 2.69/1.00                [splitting(split),new_symbols(definition,[])],
% 2.69/1.00                [c_344]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1958,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2618,plain,
% 2.69/1.00      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1958]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2723,plain,
% 2.69/1.00      ( sK1(sK3) != sK1(sK3)
% 2.69/1.00      | sK1(sK3) = sK0(sK3)
% 2.69/1.00      | sK0(sK3) != sK1(sK3) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2618]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1952,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.69/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.69/1.00      | X0 = X1
% 2.69/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.69/1.00      | ~ sP0_iProver_split ),
% 2.69/1.00      inference(splitting,
% 2.69/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.69/1.00                [c_344]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3225,plain,
% 2.69/1.00      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.69/1.00      | ~ sP0_iProver_split
% 2.69/1.00      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.69/1.00      | sK0(sK3) = sK1(sK3) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1952]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3235,plain,
% 2.69/1.00      ( v2_funct_1(sK3) ),
% 2.69/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3233]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4126,plain,
% 2.69/1.00      ( sK2 = k1_xboole_0 ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_4124,c_19,c_571,c_662,c_753,c_844,c_1975,c_1982,
% 2.69/1.00                 c_1953,c_2545,c_2723,c_3225,c_3235]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4136,plain,
% 2.69/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4126,c_2712]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4140,plain,
% 2.69/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4126,c_2356]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_0,plain,
% 2.69/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_247,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.69/1.00      | X0 != X2
% 2.69/1.00      | k1_xboole_0 != X1
% 2.69/1.00      | k1_xboole_0 = X2 ),
% 2.69/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_248,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 2.69/1.00      inference(unflattening,[status(thm)],[c_247]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2355,plain,
% 2.69/1.00      ( k1_xboole_0 = X0
% 2.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3599,plain,
% 2.69/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 2.69/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2363,c_2355]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4251,plain,
% 2.69/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_4140,c_3599]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4869,plain,
% 2.69/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.69/1.00      inference(light_normalisation,[status(thm)],[c_4136,c_4251]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2348,plain,
% 2.69/1.00      ( X0 = X1
% 2.69/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.69/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | sP0_iProver_split != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1952]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3444,plain,
% 2.69/1.00      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.69/1.00      | sK5 = X0
% 2.69/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | sP0_iProver_split != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_3242,c_2348]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1983,plain,
% 2.69/1.00      ( v1_relat_1(sK3) != iProver_top
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top
% 2.69/1.00      | sP0_iProver_split = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3762,plain,
% 2.69/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | sK5 = X0
% 2.69/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4) ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_3444,c_22,c_24,c_49,c_52,c_55,c_58,c_1983,c_2546,
% 2.69/1.00                 c_2616,c_2935,c_3081,c_3085]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3763,plain,
% 2.69/1.00      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.69/1.00      | sK5 = X0
% 2.69/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 2.69/1.00      inference(renaming,[status(thm)],[c_3762]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3773,plain,
% 2.69/1.00      ( sK5 = sK4
% 2.69/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.69/1.00      inference(equality_resolution,[status(thm)],[c_3763]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3831,plain,
% 2.69/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.69/1.00      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_3773,c_22,c_24,c_30,c_31,c_49,c_52,c_55,c_58,c_1983,
% 2.69/1.00                 c_2546,c_2616,c_2935,c_3081,c_3085,c_3177]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4871,plain,
% 2.69/1.00      ( r2_hidden(sK5,k1_xboole_0) != iProver_top
% 2.69/1.00      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4869,c_3831]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4139,plain,
% 2.69/1.00      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4126,c_2358]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4138,plain,
% 2.69/1.00      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 2.69/1.00      | v2_funct_1(sK3) != iProver_top ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_4126,c_2359]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(contradiction,plain,
% 2.69/1.00      ( $false ),
% 2.69/1.00      inference(minisat,[status(thm)],[c_4871,c_4139,c_4138,c_3233]) ).
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  ------                               Statistics
% 2.69/1.00  
% 2.69/1.00  ------ General
% 2.69/1.00  
% 2.69/1.00  abstr_ref_over_cycles:                  0
% 2.69/1.00  abstr_ref_under_cycles:                 0
% 2.69/1.00  gc_basic_clause_elim:                   0
% 2.69/1.00  forced_gc_time:                         0
% 2.69/1.00  parsing_time:                           0.012
% 2.69/1.00  unif_index_cands_time:                  0.
% 2.69/1.00  unif_index_add_time:                    0.
% 2.69/1.00  orderings_time:                         0.
% 2.69/1.00  out_proof_time:                         0.011
% 2.69/1.00  total_time:                             0.148
% 2.69/1.00  num_of_symbols:                         53
% 2.69/1.00  num_of_terms:                           2612
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing
% 2.69/1.00  
% 2.69/1.00  num_of_splits:                          2
% 2.69/1.00  num_of_split_atoms:                     2
% 2.69/1.00  num_of_reused_defs:                     0
% 2.69/1.00  num_eq_ax_congr_red:                    15
% 2.69/1.00  num_of_sem_filtered_clauses:            1
% 2.69/1.00  num_of_subtypes:                        0
% 2.69/1.00  monotx_restored_types:                  0
% 2.69/1.00  sat_num_of_epr_types:                   0
% 2.69/1.00  sat_num_of_non_cyclic_types:            0
% 2.69/1.00  sat_guarded_non_collapsed_types:        0
% 2.69/1.00  num_pure_diseq_elim:                    0
% 2.69/1.00  simp_replaced_by:                       0
% 2.69/1.00  res_preprocessed:                       110
% 2.69/1.00  prep_upred:                             0
% 2.69/1.00  prep_unflattend:                        20
% 2.69/1.00  smt_new_axioms:                         0
% 2.69/1.00  pred_elim_cands:                        4
% 2.69/1.00  pred_elim:                              3
% 2.69/1.00  pred_elim_cl:                           3
% 2.69/1.00  pred_elim_cycles:                       7
% 2.69/1.00  merged_defs:                            0
% 2.69/1.00  merged_defs_ncl:                        0
% 2.69/1.00  bin_hyper_res:                          0
% 2.69/1.00  prep_cycles:                            4
% 2.69/1.00  pred_elim_time:                         0.024
% 2.69/1.00  splitting_time:                         0.
% 2.69/1.00  sem_filter_time:                        0.
% 2.69/1.00  monotx_time:                            0.001
% 2.69/1.00  subtype_inf_time:                       0.
% 2.69/1.00  
% 2.69/1.00  ------ Problem properties
% 2.69/1.00  
% 2.69/1.00  clauses:                                21
% 2.69/1.00  conjectures:                            6
% 2.69/1.00  epr:                                    5
% 2.69/1.00  horn:                                   16
% 2.69/1.00  ground:                                 11
% 2.69/1.00  unary:                                  2
% 2.69/1.00  binary:                                 8
% 2.69/1.00  lits:                                   55
% 2.69/1.00  lits_eq:                                12
% 2.69/1.00  fd_pure:                                0
% 2.69/1.00  fd_pseudo:                              0
% 2.69/1.00  fd_cond:                                1
% 2.69/1.00  fd_pseudo_cond:                         2
% 2.69/1.00  ac_symbols:                             0
% 2.69/1.00  
% 2.69/1.00  ------ Propositional Solver
% 2.69/1.00  
% 2.69/1.00  prop_solver_calls:                      28
% 2.69/1.00  prop_fast_solver_calls:                 1064
% 2.69/1.00  smt_solver_calls:                       0
% 2.69/1.00  smt_fast_solver_calls:                  0
% 2.69/1.00  prop_num_of_clauses:                    1217
% 2.69/1.00  prop_preprocess_simplified:             4524
% 2.69/1.00  prop_fo_subsumed:                       17
% 2.69/1.00  prop_solver_time:                       0.
% 2.69/1.00  smt_solver_time:                        0.
% 2.69/1.00  smt_fast_solver_time:                   0.
% 2.69/1.00  prop_fast_solver_time:                  0.
% 2.69/1.00  prop_unsat_core_time:                   0.
% 2.69/1.00  
% 2.69/1.00  ------ QBF
% 2.69/1.00  
% 2.69/1.00  qbf_q_res:                              0
% 2.69/1.00  qbf_num_tautologies:                    0
% 2.69/1.00  qbf_prep_cycles:                        0
% 2.69/1.00  
% 2.69/1.00  ------ BMC1
% 2.69/1.00  
% 2.69/1.00  bmc1_current_bound:                     -1
% 2.69/1.00  bmc1_last_solved_bound:                 -1
% 2.69/1.00  bmc1_unsat_core_size:                   -1
% 2.69/1.00  bmc1_unsat_core_parents_size:           -1
% 2.69/1.00  bmc1_merge_next_fun:                    0
% 2.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation
% 2.69/1.00  
% 2.69/1.00  inst_num_of_clauses:                    372
% 2.69/1.00  inst_num_in_passive:                    4
% 2.69/1.00  inst_num_in_active:                     284
% 2.69/1.00  inst_num_in_unprocessed:                85
% 2.69/1.00  inst_num_of_loops:                      320
% 2.69/1.00  inst_num_of_learning_restarts:          0
% 2.69/1.00  inst_num_moves_active_passive:          32
% 2.69/1.00  inst_lit_activity:                      0
% 2.69/1.00  inst_lit_activity_moves:                0
% 2.69/1.00  inst_num_tautologies:                   0
% 2.69/1.00  inst_num_prop_implied:                  0
% 2.69/1.00  inst_num_existing_simplified:           0
% 2.69/1.00  inst_num_eq_res_simplified:             0
% 2.69/1.00  inst_num_child_elim:                    0
% 2.69/1.00  inst_num_of_dismatching_blockings:      92
% 2.69/1.00  inst_num_of_non_proper_insts:           489
% 2.69/1.00  inst_num_of_duplicates:                 0
% 2.69/1.00  inst_inst_num_from_inst_to_res:         0
% 2.69/1.00  inst_dismatching_checking_time:         0.
% 2.69/1.00  
% 2.69/1.00  ------ Resolution
% 2.69/1.00  
% 2.69/1.00  res_num_of_clauses:                     0
% 2.69/1.00  res_num_in_passive:                     0
% 2.69/1.00  res_num_in_active:                      0
% 2.69/1.00  res_num_of_loops:                       114
% 2.69/1.00  res_forward_subset_subsumed:            51
% 2.69/1.00  res_backward_subset_subsumed:           4
% 2.69/1.00  res_forward_subsumed:                   0
% 2.69/1.00  res_backward_subsumed:                  0
% 2.69/1.00  res_forward_subsumption_resolution:     0
% 2.69/1.00  res_backward_subsumption_resolution:    0
% 2.69/1.00  res_clause_to_clause_subsumption:       128
% 2.69/1.00  res_orphan_elimination:                 0
% 2.69/1.00  res_tautology_del:                      61
% 2.69/1.00  res_num_eq_res_simplified:              0
% 2.69/1.00  res_num_sel_changes:                    0
% 2.69/1.00  res_moves_from_active_to_pass:          0
% 2.69/1.00  
% 2.69/1.00  ------ Superposition
% 2.69/1.00  
% 2.69/1.00  sup_time_total:                         0.
% 2.69/1.00  sup_time_generating:                    0.
% 2.69/1.00  sup_time_sim_full:                      0.
% 2.69/1.00  sup_time_sim_immed:                     0.
% 2.69/1.00  
% 2.69/1.00  sup_num_of_clauses:                     68
% 2.69/1.00  sup_num_in_active:                      40
% 2.69/1.00  sup_num_in_passive:                     28
% 2.69/1.00  sup_num_of_loops:                       62
% 2.69/1.00  sup_fw_superposition:                   30
% 2.69/1.00  sup_bw_superposition:                   55
% 2.69/1.00  sup_immediate_simplified:               12
% 2.69/1.00  sup_given_eliminated:                   3
% 2.69/1.00  comparisons_done:                       0
% 2.69/1.00  comparisons_avoided:                    6
% 2.69/1.00  
% 2.69/1.00  ------ Simplifications
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  sim_fw_subset_subsumed:                 5
% 2.69/1.00  sim_bw_subset_subsumed:                 1
% 2.69/1.00  sim_fw_subsumed:                        2
% 2.69/1.00  sim_bw_subsumed:                        2
% 2.69/1.00  sim_fw_subsumption_res:                 0
% 2.69/1.00  sim_bw_subsumption_res:                 0
% 2.69/1.00  sim_tautology_del:                      0
% 2.69/1.00  sim_eq_tautology_del:                   7
% 2.69/1.00  sim_eq_res_simp:                        0
% 2.69/1.00  sim_fw_demodulated:                     3
% 2.69/1.00  sim_bw_demodulated:                     23
% 2.69/1.00  sim_light_normalised:                   2
% 2.69/1.00  sim_joinable_taut:                      0
% 2.69/1.00  sim_joinable_simp:                      0
% 2.69/1.00  sim_ac_normalised:                      0
% 2.69/1.00  sim_smt_subsumption:                    0
% 2.69/1.00  
%------------------------------------------------------------------------------
