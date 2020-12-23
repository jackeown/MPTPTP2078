%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:39 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_8121)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f17])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK6) != k1_funct_1(X3,sK6)
        & r2_hidden(sK6,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ( ? [X4] :
              ( k1_funct_1(sK5,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ r1_partfun1(X2,sK5) )
        & ( ! [X5] :
              ( k1_funct_1(sK5,X5) = k1_funct_1(X2,X5)
              | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
          | r1_partfun1(X2,sK5) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(sK4,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(sK2,sK3,sK4)) )
            | ~ r1_partfun1(sK4,X3) )
          & ( ! [X5] :
                ( k1_funct_1(sK4,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) )
            | r1_partfun1(sK4,X3) )
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
        & r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) )
      | ~ r1_partfun1(sK4,sK5) )
    & ( ! [X5] :
          ( k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) )
      | r1_partfun1(sK4,sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f64,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))
      | r1_partfun1(sK4,sK5) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,
    ( r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4))
    | ~ r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
    | ~ r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_345,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_347,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_24])).

cnf(c_1440,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1447,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2111,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1440,c_1447])).

cnf(c_2182,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_347,c_2111])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1455,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1438,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2112,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1438,c_1447])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1448,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2482,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_1448])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3156,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2482,c_30])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1450,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3161,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_1450])).

cnf(c_3514,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_3161])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1456,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4734,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_1456])).

cnf(c_18,plain,
    ( r1_partfun1(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1445,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1454,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2873,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1454])).

cnf(c_7156,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_2873])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1640,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1641,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_7546,plain,
    ( v1_relat_1(X0) != iProver_top
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7156,c_31,c_33,c_1641])).

cnf(c_7547,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7546])).

cnf(c_2327,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2111,c_1448])).

cnf(c_3141,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_33])).

cnf(c_3147,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_1450])).

cnf(c_7563,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK5)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7547,c_3147])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_76,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_78,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_82,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1028,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1794,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1795,plain,
    ( sK2 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_1797,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_1027,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1663,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_1884,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1026,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1885,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_2595,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_2596,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_1451,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1452,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2872,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK5,X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_1445])).

cnf(c_3485,plain,
    ( r1_partfun1(sK5,X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_3147])).

cnf(c_3646,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_partfun1(sK5,X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2872,c_31,c_33,c_1641,c_3485])).

cnf(c_3647,plain,
    ( r1_partfun1(sK5,X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3646])).

cnf(c_3657,plain,
    ( r1_partfun1(sK5,sK5) = iProver_top
    | r2_hidden(sK1(sK5,sK5),sK2) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_3647])).

cnf(c_4489,plain,
    ( r1_partfun1(sK5,sK5) = iProver_top
    | r2_hidden(sK1(sK5,sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3657,c_31,c_33,c_1641])).

cnf(c_4495,plain,
    ( r1_partfun1(sK5,sK5) = iProver_top
    | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_1454])).

cnf(c_5512,plain,
    ( r1_partfun1(sK5,sK5) = iProver_top
    | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4495,c_1454])).

cnf(c_9095,plain,
    ( r1_partfun1(sK5,sK5) = iProver_top
    | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_5512])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1643,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1691,plain,
    ( r1_partfun1(X0,sK5)
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1761,plain,
    ( r1_partfun1(sK4,sK5)
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_17,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1701,plain,
    ( r1_partfun1(X0,sK5)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(X0,sK5)) != k1_funct_1(X0,sK1(X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1773,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_1832,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | k1_relat_1(sK5) != X1
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1834,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_3220,plain,
    ( r2_hidden(sK1(sK4,sK5),X0)
    | ~ r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3222,plain,
    ( ~ r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
    | r2_hidden(sK1(sK4,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_4894,plain,
    ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3484,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_3147])).

cnf(c_4245,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_1454])).

cnf(c_5625,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4245,c_1456])).

cnf(c_1453,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5693,plain,
    ( k1_relat_1(sK5) = X0
    | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5625,c_1453])).

cnf(c_5734,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5693])).

cnf(c_22,negated_conjecture,
    ( r1_partfun1(sK4,sK5)
    | ~ r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6220,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4735,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_1454])).

cnf(c_6778,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_1456])).

cnf(c_7252,plain,
    ( k1_relat_1(sK4) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6778,c_1453])).

cnf(c_7328,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7252])).

cnf(c_21,negated_conjecture,
    ( ~ r1_partfun1(sK4,sK5)
    | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1442,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2458,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2112,c_1442])).

cnf(c_2487,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_1454])).

cnf(c_7257,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6778,c_2487])).

cnf(c_29,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,negated_conjecture,
    ( ~ r1_partfun1(sK4,sK5)
    | k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
    | r1_partfun1(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1644,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_1670,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2280,plain,
    ( ~ r1_partfun1(X0,sK5)
    | ~ r2_hidden(sK6,k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK6) = k1_funct_1(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3844,plain,
    ( ~ r1_partfun1(sK4,sK5)
    | ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_3845,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_1444,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r1_partfun1(X2,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2603,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_1444])).

cnf(c_3933,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_31,c_33,c_1641])).

cnf(c_3934,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3933])).

cnf(c_3948,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_3934])).

cnf(c_4078,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3948,c_29,c_30,c_1644])).

cnf(c_4859,plain,
    ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4862,plain,
    ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4859])).

cnf(c_2079,plain,
    ( k1_funct_1(sK5,sK6) != X0
    | k1_funct_1(sK4,sK6) != X0
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_2279,plain,
    ( k1_funct_1(sK5,sK6) != k1_funct_1(X0,sK6)
    | k1_funct_1(sK4,sK6) != k1_funct_1(X0,sK6)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_5559,plain,
    ( k1_funct_1(sK5,sK6) != k1_funct_1(sK4,sK6)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6)
    | k1_funct_1(sK4,sK6) != k1_funct_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_2532,plain,
    ( X0 != X1
    | X0 = k1_relset_1(sK2,sK3,sK5)
    | k1_relset_1(sK2,sK3,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_5032,plain,
    ( X0 = k1_relset_1(sK2,sK3,sK5)
    | X0 != k1_relat_1(sK5)
    | k1_relset_1(sK2,sK3,sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_5605,plain,
    ( k1_relset_1(sK2,sK3,sK5) != k1_relat_1(sK5)
    | k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5032])).

cnf(c_5606,plain,
    ( k1_relat_1(sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_2306,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_1453])).

cnf(c_7256,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6778,c_2306])).

cnf(c_7351,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_7382,plain,
    ( ~ r1_tarski(X0,k1_relset_1(sK2,sK3,sK5))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_7383,plain,
    ( k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
    | k1_relat_1(sK4) != X0
    | r1_tarski(X0,k1_relset_1(sK2,sK3,sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7382])).

cnf(c_7385,plain,
    ( k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
    | k1_relat_1(sK4) != k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7383])).

cnf(c_8116,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7257,c_29,c_30,c_31,c_24,c_33,c_23,c_38,c_77,c_78,c_82,c_1641,c_1644,c_1670,c_1797,c_1884,c_1885,c_2458,c_2596,c_3845,c_4078,c_4734,c_4862,c_5559,c_5605,c_5606,c_7256,c_7351,c_7385])).

cnf(c_8118,plain,
    ( ~ r1_partfun1(sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8116])).

cnf(c_8311,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK4),X2)
    | X2 != X1
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_8313,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8311])).

cnf(c_3235,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != X0
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_5572,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5))
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3235])).

cnf(c_8471,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5))
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_5572])).

cnf(c_8472,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_8809,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8812,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8809])).

cnf(c_8832,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8835,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8832])).

cnf(c_6163,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
    | ~ r1_tarski(X1,k1_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10768,plain,
    ( ~ r2_hidden(sK1(sK4,sK5),X0)
    | r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
    | ~ r1_tarski(X0,k1_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6163])).

cnf(c_10770,plain,
    ( r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(sK1(sK4,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10768])).

cnf(c_10830,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9095,c_28,c_27,c_26,c_24,c_77,c_82,c_1640,c_1643,c_1761,c_1773,c_1834,c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770])).

cnf(c_11102,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK5)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7563,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770])).

cnf(c_11119,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_11102])).

cnf(c_11259,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11119,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770])).

cnf(c_11270,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK5),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11259,c_1454])).

cnf(c_1441,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r1_partfun1(sK4,sK5) = iProver_top
    | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2457,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK4,sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2112,c_1441])).

cnf(c_11283,plain,
    ( k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
    | r1_partfun1(X0,sK5) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11270,c_2457])).

cnf(c_11462,plain,
    ( r1_partfun1(X0,sK5) = iProver_top
    | k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11283,c_29,c_30,c_31,c_24,c_33,c_23,c_38,c_77,c_78,c_82,c_1641,c_1644,c_1670,c_1797,c_1884,c_1885,c_2458,c_2596,c_3845,c_4078,c_4734,c_4862,c_5559,c_5605,c_5606,c_7256,c_7351,c_7385])).

cnf(c_11463,plain,
    ( k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
    | r1_partfun1(X0,sK5) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11462])).

cnf(c_11478,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_11463])).

cnf(c_2874,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_2457])).

cnf(c_3783,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2874,c_29,c_30,c_1644])).

cnf(c_3784,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3783])).

cnf(c_3797,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_3784])).

cnf(c_3922,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_31,c_33,c_1641])).

cnf(c_11499,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11478,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8121,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770])).

cnf(c_1446,plain,
    ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11502,plain,
    ( r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11499,c_1446])).

cnf(c_1774,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5))
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1773])).

cnf(c_16394,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11502,c_28,c_29,c_27,c_30,c_26,c_31,c_24,c_33,c_23,c_38,c_77,c_78,c_82,c_1640,c_1641,c_1643,c_1644,c_1670,c_1761,c_1773,c_1774,c_1797,c_1834,c_1884,c_1885,c_2458,c_2596,c_3222,c_3845,c_4078,c_4734,c_4862,c_4894,c_5559,c_5605,c_5606,c_5734,c_6220,c_7328,c_7256,c_7351,c_7385,c_8118,c_8121,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770])).

cnf(c_16402,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_16394])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16402,c_10830,c_4734,c_2596,c_1885,c_1884,c_1797,c_82,c_78,c_77,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.97/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.97  
% 3.97/0.97  ------  iProver source info
% 3.97/0.97  
% 3.97/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.97  git: non_committed_changes: false
% 3.97/0.97  git: last_make_outside_of_git: false
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     num_symb
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       true
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  ------ Parsing...
% 3.97/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.97  ------ Proving...
% 3.97/0.97  ------ Problem Properties 
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  clauses                                 24
% 3.97/0.97  conjectures                             8
% 3.97/0.97  EPR                                     7
% 3.97/0.97  Horn                                    19
% 3.97/0.97  unary                                   6
% 3.97/0.97  binary                                  9
% 3.97/0.97  lits                                    65
% 3.97/0.97  lits eq                                 15
% 3.97/0.97  fd_pure                                 0
% 3.97/0.97  fd_pseudo                               0
% 3.97/0.97  fd_cond                                 0
% 3.97/0.97  fd_pseudo_cond                          1
% 3.97/0.97  AC symbols                              0
% 3.97/0.97  
% 3.97/0.97  ------ Schedule dynamic 5 is on 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  Current options:
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     none
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       false
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ Proving...
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS status Theorem for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  fof(f8,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f17,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f8])).
% 3.97/0.97  
% 3.97/0.97  fof(f18,plain,(
% 3.97/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(flattening,[],[f17])).
% 3.97/0.97  
% 3.97/0.97  fof(f29,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(nnf_transformation,[],[f18])).
% 3.97/0.97  
% 3.97/0.97  fof(f52,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f29])).
% 3.97/0.97  
% 3.97/0.97  fof(f10,conjecture,(
% 3.97/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f11,negated_conjecture,(
% 3.97/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 3.97/0.97    inference(negated_conjecture,[],[f10])).
% 3.97/0.97  
% 3.97/0.97  fof(f21,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.97/0.97    inference(ennf_transformation,[],[f11])).
% 3.97/0.97  
% 3.97/0.97  fof(f22,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.97/0.97    inference(flattening,[],[f21])).
% 3.97/0.97  
% 3.97/0.97  fof(f34,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.97/0.97    inference(nnf_transformation,[],[f22])).
% 3.97/0.97  
% 3.97/0.97  fof(f35,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.97/0.97    inference(flattening,[],[f34])).
% 3.97/0.97  
% 3.97/0.97  fof(f36,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.97/0.97    inference(rectify,[],[f35])).
% 3.97/0.97  
% 3.97/0.97  fof(f39,plain,(
% 3.97/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK6) != k1_funct_1(X3,sK6) & r2_hidden(sK6,k1_relset_1(X0,X1,X2)))) )),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f38,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK5,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK5)) & (! [X5] : (k1_funct_1(sK5,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK5)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f37,plain,(
% 3.97/0.97    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK2,sK3,sK4))) | ~r1_partfun1(sK4,X3)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))) | r1_partfun1(sK4,X3)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f40,plain,(
% 3.97/0.97    (((k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) & r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4))) | ~r1_partfun1(sK4,sK5)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))) | r1_partfun1(sK4,sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 3.97/0.97  
% 3.97/0.97  fof(f64,plain,(
% 3.97/0.97    v1_funct_2(sK5,sK2,sK3)),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f65,plain,(
% 3.97/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f7,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f16,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f7])).
% 3.97/0.97  
% 3.97/0.97  fof(f51,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f16])).
% 3.97/0.97  
% 3.97/0.97  fof(f1,axiom,(
% 3.97/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f12,plain,(
% 3.97/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.97/0.97    inference(ennf_transformation,[],[f1])).
% 3.97/0.97  
% 3.97/0.97  fof(f23,plain,(
% 3.97/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/0.97    inference(nnf_transformation,[],[f12])).
% 3.97/0.97  
% 3.97/0.97  fof(f24,plain,(
% 3.97/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/0.97    inference(rectify,[],[f23])).
% 3.97/0.97  
% 3.97/0.97  fof(f25,plain,(
% 3.97/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f26,plain,(
% 3.97/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.97/0.97  
% 3.97/0.97  fof(f42,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f26])).
% 3.97/0.97  
% 3.97/0.97  fof(f62,plain,(
% 3.97/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f6,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f15,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f6])).
% 3.97/0.97  
% 3.97/0.97  fof(f50,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f15])).
% 3.97/0.97  
% 3.97/0.97  fof(f4,axiom,(
% 3.97/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f13,plain,(
% 3.97/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.97/0.97    inference(ennf_transformation,[],[f4])).
% 3.97/0.97  
% 3.97/0.97  fof(f48,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f13])).
% 3.97/0.97  
% 3.97/0.97  fof(f43,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f26])).
% 3.97/0.97  
% 3.97/0.97  fof(f9,axiom,(
% 3.97/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f19,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.97/0.97    inference(ennf_transformation,[],[f9])).
% 3.97/0.97  
% 3.97/0.97  fof(f20,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.97    inference(flattening,[],[f19])).
% 3.97/0.97  
% 3.97/0.97  fof(f30,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.97    inference(nnf_transformation,[],[f20])).
% 3.97/0.97  
% 3.97/0.97  fof(f31,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.97    inference(rectify,[],[f30])).
% 3.97/0.97  
% 3.97/0.97  fof(f32,plain,(
% 3.97/0.97    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f33,plain,(
% 3.97/0.97    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.97/0.97  
% 3.97/0.97  fof(f59,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f33])).
% 3.97/0.97  
% 3.97/0.97  fof(f41,plain,(
% 3.97/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f26])).
% 3.97/0.97  
% 3.97/0.97  fof(f63,plain,(
% 3.97/0.97    v1_funct_1(sK5)),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f5,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f14,plain,(
% 3.97/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/0.97    inference(ennf_transformation,[],[f5])).
% 3.97/0.97  
% 3.97/0.97  fof(f49,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f14])).
% 3.97/0.97  
% 3.97/0.97  fof(f66,plain,(
% 3.97/0.97    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f3,axiom,(
% 3.97/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f47,plain,(
% 3.97/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f3])).
% 3.97/0.97  
% 3.97/0.97  fof(f2,axiom,(
% 3.97/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f27,plain,(
% 3.97/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.97    inference(nnf_transformation,[],[f2])).
% 3.97/0.97  
% 3.97/0.97  fof(f28,plain,(
% 3.97/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.97    inference(flattening,[],[f27])).
% 3.97/0.97  
% 3.97/0.97  fof(f46,plain,(
% 3.97/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f28])).
% 3.97/0.97  
% 3.97/0.97  fof(f44,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.97/0.97    inference(cnf_transformation,[],[f28])).
% 3.97/0.97  
% 3.97/0.97  fof(f71,plain,(
% 3.97/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.97/0.97    inference(equality_resolution,[],[f44])).
% 3.97/0.97  
% 3.97/0.97  fof(f61,plain,(
% 3.97/0.97    v1_funct_1(sK4)),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f60,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f33])).
% 3.97/0.97  
% 3.97/0.97  fof(f67,plain,(
% 3.97/0.97    ( ! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) | r1_partfun1(sK4,sK5)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f68,plain,(
% 3.97/0.97    r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) | ~r1_partfun1(sK4,sK5)),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f69,plain,(
% 3.97/0.97    k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) | ~r1_partfun1(sK4,sK5)),
% 3.97/0.97    inference(cnf_transformation,[],[f40])).
% 3.97/0.97  
% 3.97/0.97  fof(f58,plain,(
% 3.97/0.97    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f33])).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16,plain,
% 3.97/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.97/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.97/0.97      | k1_xboole_0 = X2 ),
% 3.97/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_25,negated_conjecture,
% 3.97/0.97      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.97/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_344,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.97/0.97      | sK3 != X2
% 3.97/0.97      | sK2 != X1
% 3.97/0.97      | sK5 != X0
% 3.97/0.97      | k1_xboole_0 = X2 ),
% 3.97/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_345,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.97/0.97      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.97/0.97      | k1_xboole_0 = sK3 ),
% 3.97/0.97      inference(unflattening,[status(thm)],[c_344]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_24,negated_conjecture,
% 3.97/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.97/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_347,plain,
% 3.97/0.97      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_345,c_24]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1440,plain,
% 3.97/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1447,plain,
% 3.97/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.97/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2111,plain,
% 3.97/0.97      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1440,c_1447]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2182,plain,
% 3.97/0.97      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_347,c_2111]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1,plain,
% 3.97/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1455,plain,
% 3.97/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.97/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_27,negated_conjecture,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.97/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1438,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2112,plain,
% 3.97/0.97      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1438,c_1447]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_9,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1448,plain,
% 3.97/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.97/0.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2482,plain,
% 3.97/0.97      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 3.97/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2112,c_1448]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_30,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3156,plain,
% 3.97/0.97      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_2482,c_30]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.97/0.97      | ~ r2_hidden(X2,X0)
% 3.97/0.97      | r2_hidden(X2,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1450,plain,
% 3.97/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.97/0.97      | r2_hidden(X2,X0) != iProver_top
% 3.97/0.97      | r2_hidden(X2,X1) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3161,plain,
% 3.97/0.97      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | r2_hidden(X0,sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3156,c_1450]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3514,plain,
% 3.97/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1455,c_3161]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_0,plain,
% 3.97/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1456,plain,
% 3.97/0.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.97/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4734,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3514,c_1456]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_18,plain,
% 3.97/0.97      ( r1_partfun1(X0,X1)
% 3.97/0.97      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/0.97      | ~ v1_funct_1(X1)
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | ~ v1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1445,plain,
% 3.97/0.97      ( r1_partfun1(X0,X1) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.97/0.97      | v1_funct_1(X1) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X1) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2,plain,
% 3.97/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1454,plain,
% 3.97/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.97/0.97      | r2_hidden(X0,X2) = iProver_top
% 3.97/0.97      | r1_tarski(X1,X2) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2873,plain,
% 3.97/0.97      ( r1_partfun1(X0,X1) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.97/0.97      | v1_funct_1(X1) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X1) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1445,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7156,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_2873]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_26,negated_conjecture,
% 3.97/0.97      ( v1_funct_1(sK5) ),
% 3.97/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_31,plain,
% 3.97/0.97      ( v1_funct_1(sK5) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_33,plain,
% 3.97/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8,plain,
% 3.97/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/0.97      | v1_relat_1(X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1640,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.97/0.97      | v1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1641,plain,
% 3.97/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7546,plain,
% 3.97/0.97      ( v1_relat_1(X0) != iProver_top
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_7156,c_31,c_33,c_1641]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7547,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_7546]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2327,plain,
% 3.97/0.97      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 3.97/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2111,c_1448]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3141,plain,
% 3.97/0.97      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_2327,c_33]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3147,plain,
% 3.97/0.97      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | r2_hidden(X0,sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3141,c_1450]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7563,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_7547,c_3147]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_23,negated_conjecture,
% 3.97/0.97      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.97/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_77,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_76,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_78,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_76]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.97/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_82,plain,
% 3.97/0.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.97/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1028,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.97/0.97      theory(equality) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1794,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1)
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0)
% 3.97/0.97      | sK2 != X0
% 3.97/0.97      | k1_xboole_0 != X1 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1795,plain,
% 3.97/0.97      ( sK2 != X0
% 3.97/0.97      | k1_xboole_0 != X1
% 3.97/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1797,plain,
% 3.97/0.97      ( sK2 != k1_xboole_0
% 3.97/0.97      | k1_xboole_0 != k1_xboole_0
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.97/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1795]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1027,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1663,plain,
% 3.97/0.97      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1884,plain,
% 3.97/0.97      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1663]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1026,plain,( X0 = X0 ),theory(equality) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1885,plain,
% 3.97/0.97      ( sK2 = sK2 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2595,plain,
% 3.97/0.97      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2596,plain,
% 3.97/0.97      ( sK3 != k1_xboole_0
% 3.97/0.97      | k1_xboole_0 = sK3
% 3.97/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2595]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1451,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5,plain,
% 3.97/0.97      ( r1_tarski(X0,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1452,plain,
% 3.97/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2872,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(sK5,X0) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_1445]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3485,plain,
% 3.97/0.97      ( r1_partfun1(sK5,X0) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1445,c_3147]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3646,plain,
% 3.97/0.97      ( v1_relat_1(X0) != iProver_top
% 3.97/0.97      | r1_partfun1(sK5,X0) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_2872,c_31,c_33,c_1641,c_3485]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3647,plain,
% 3.97/0.97      ( r1_partfun1(sK5,X0) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_3646]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3657,plain,
% 3.97/0.97      ( r1_partfun1(sK5,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,sK5),sK2) = iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1452,c_3647]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4489,plain,
% 3.97/0.97      ( r1_partfun1(sK5,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,sK5),sK2) = iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_3657,c_31,c_33,c_1641]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4495,plain,
% 3.97/0.97      ( r1_partfun1(sK5,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_4489,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5512,plain,
% 3.97/0.97      ( r1_partfun1(sK5,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
% 3.97/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,X1) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_4495,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_9095,plain,
% 3.97/0.97      ( r1_partfun1(sK5,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(sK5,sK5),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1451,c_5512]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_28,negated_conjecture,
% 3.97/0.97      ( v1_funct_1(sK4) ),
% 3.97/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1643,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.97/0.97      | v1_relat_1(sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1691,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5)
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | ~ v1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1761,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5)
% 3.97/0.97      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_relat_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(sK4) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1691]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_17,plain,
% 3.97/0.97      ( r1_partfun1(X0,X1)
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/0.97      | ~ v1_funct_1(X1)
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1701,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5)
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | ~ v1_relat_1(sK5)
% 3.97/0.97      | k1_funct_1(sK5,sK1(X0,sK5)) != k1_funct_1(X0,sK1(X0,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_17]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1773,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5)
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_relat_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(sK4)
% 3.97/0.97      | k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1701]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1832,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1)
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | k1_relat_1(sK5) != X1
% 3.97/0.97      | k1_relat_1(sK4) != X0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1834,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.97/0.97      | k1_relat_1(sK5) != k1_xboole_0
% 3.97/0.97      | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1832]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3220,plain,
% 3.97/0.97      ( r2_hidden(sK1(sK4,sK5),X0)
% 3.97/0.97      | ~ r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(sK4),X0) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3222,plain,
% 3.97/0.97      ( ~ r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4))
% 3.97/0.97      | r2_hidden(sK1(sK4,sK5),k1_xboole_0)
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_3220]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4894,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK4)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3484,plain,
% 3.97/0.97      ( r2_hidden(sK0(k1_relat_1(sK5),X0),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1455,c_3147]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4245,plain,
% 3.97/0.97      ( r2_hidden(sK0(k1_relat_1(sK5),X0),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X1) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3484,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5625,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_4245,c_1456]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1453,plain,
% 3.97/0.97      ( X0 = X1
% 3.97/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.97/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5693,plain,
% 3.97/0.97      ( k1_relat_1(sK5) = X0
% 3.97/0.97      | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_5625,c_1453]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5734,plain,
% 3.97/0.97      ( k1_relat_1(sK5) = k1_xboole_0
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.97/0.97      | r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_5693]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_22,negated_conjecture,
% 3.97/0.97      ( r1_partfun1(sK4,sK5)
% 3.97/0.97      | ~ r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
% 3.97/0.97      | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6220,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5)
% 3.97/0.97      | ~ r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
% 3.97/0.97      | k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_22]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4735,plain,
% 3.97/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),X0),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X1) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3514,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6778,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_4735,c_1456]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7252,plain,
% 3.97/0.97      ( k1_relat_1(sK4) = X0
% 3.97/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_6778,c_1453]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7328,plain,
% 3.97/0.97      ( k1_relat_1(sK4) = k1_xboole_0
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.97/0.97      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_7252]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_21,negated_conjecture,
% 3.97/0.97      ( ~ r1_partfun1(sK4,sK5)
% 3.97/0.97      | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1442,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2458,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_2112,c_1442]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2487,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(sK6,X0) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2458,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7257,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(sK6,X0) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_6778,c_2487]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_29,plain,
% 3.97/0.97      ( v1_funct_1(sK4) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_20,negated_conjecture,
% 3.97/0.97      ( ~ r1_partfun1(sK4,sK5)
% 3.97/0.97      | k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) ),
% 3.97/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_38,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
% 3.97/0.97      | r1_partfun1(sK4,sK5) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1644,plain,
% 3.97/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1670,plain,
% 3.97/0.97      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.97/0.97      | k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_19,plain,
% 3.97/0.97      ( ~ r1_partfun1(X0,X1)
% 3.97/0.97      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.97/0.97      | ~ v1_funct_1(X1)
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_relat_1(X1)
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2280,plain,
% 3.97/0.97      ( ~ r1_partfun1(X0,sK5)
% 3.97/0.97      | ~ r2_hidden(sK6,k1_relat_1(X0))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(X0)
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(X0)
% 3.97/0.97      | ~ v1_relat_1(sK5)
% 3.97/0.97      | k1_funct_1(sK5,sK6) = k1_funct_1(X0,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_19]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3844,plain,
% 3.97/0.97      ( ~ r1_partfun1(sK4,sK5)
% 3.97/0.97      | ~ r2_hidden(sK6,k1_relat_1(sK4))
% 3.97/0.97      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | ~ v1_funct_1(sK5)
% 3.97/0.97      | ~ v1_funct_1(sK4)
% 3.97/0.97      | ~ v1_relat_1(sK5)
% 3.97/0.97      | ~ v1_relat_1(sK4)
% 3.97/0.97      | k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2280]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3845,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.97/0.97      | r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1444,plain,
% 3.97/0.97      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 3.97/0.97      | r1_partfun1(X2,X0) != iProver_top
% 3.97/0.97      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(X2) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2603,plain,
% 3.97/0.97      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_1444]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3933,plain,
% 3.97/0.97      ( v1_relat_1(X0) != iProver_top
% 3.97/0.97      | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_2603,c_31,c_33,c_1641]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3934,plain,
% 3.97/0.97      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) != iProver_top
% 3.97/0.97      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_3933]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3948,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2458,c_3934]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4078,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(sK4,sK5) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_3948,c_29,c_30,c_1644]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4859,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4862,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_4859]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2079,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) != X0
% 3.97/0.97      | k1_funct_1(sK4,sK6) != X0
% 3.97/0.97      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2279,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) != k1_funct_1(X0,sK6)
% 3.97/0.97      | k1_funct_1(sK4,sK6) != k1_funct_1(X0,sK6)
% 3.97/0.97      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2079]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5559,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK6) != k1_funct_1(sK4,sK6)
% 3.97/0.97      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6)
% 3.97/0.97      | k1_funct_1(sK4,sK6) != k1_funct_1(sK4,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2279]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2532,plain,
% 3.97/0.97      ( X0 != X1
% 3.97/0.97      | X0 = k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | k1_relset_1(sK2,sK3,sK5) != X1 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5032,plain,
% 3.97/0.97      ( X0 = k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | X0 != k1_relat_1(sK5)
% 3.97/0.97      | k1_relset_1(sK2,sK3,sK5) != k1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2532]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5605,plain,
% 3.97/0.97      ( k1_relset_1(sK2,sK3,sK5) != k1_relat_1(sK5)
% 3.97/0.97      | k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | k1_relat_1(sK5) != k1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_5032]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5606,plain,
% 3.97/0.97      ( k1_relat_1(sK5) = k1_relat_1(sK5) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2306,plain,
% 3.97/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1451,c_1453]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7256,plain,
% 3.97/0.97      ( k1_relat_1(sK4) = k1_xboole_0
% 3.97/0.97      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_6778,c_2306]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7351,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK6) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7382,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k1_relset_1(sK2,sK3,sK5))
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.97/0.97      | k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | k1_relat_1(sK4) != X0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1832]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7383,plain,
% 3.97/0.97      ( k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | k1_relat_1(sK4) != X0
% 3.97/0.97      | r1_tarski(X0,k1_relset_1(sK2,sK3,sK5)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_7382]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_7385,plain,
% 3.97/0.97      ( k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
% 3.97/0.97      | k1_relat_1(sK4) != k1_xboole_0
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top
% 3.97/0.97      | r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK5)) != iProver_top ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_7383]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8116,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_7257,c_29,c_30,c_31,c_24,c_33,c_23,c_38,c_77,c_78,
% 3.97/0.97                 c_82,c_1641,c_1644,c_1670,c_1797,c_1884,c_1885,c_2458,
% 3.97/0.97                 c_2596,c_3845,c_4078,c_4734,c_4862,c_5559,c_5605,c_5606,
% 3.97/0.97                 c_7256,c_7351,c_7385]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8118,plain,
% 3.97/0.97      ( ~ r1_partfun1(sK4,sK5) ),
% 3.97/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_8116]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8311,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,X1)
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),X2)
% 3.97/0.97      | X2 != X1
% 3.97/0.97      | k1_relat_1(sK4) != X0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8313,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0)
% 3.97/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.97/0.97      | k1_relat_1(sK4) != k1_xboole_0
% 3.97/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_8311]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3235,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK1(sK4,sK5)) != X0
% 3.97/0.97      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.97/0.97      | k1_funct_1(sK4,sK1(sK4,sK5)) != X0 ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_5572,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5))
% 3.97/0.97      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.97/0.97      | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_3235]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8471,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5))
% 3.97/0.97      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.97/0.97      | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_5572]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8472,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8809,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8812,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_8809]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8832,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8835,plain,
% 3.97/0.97      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_8832]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_6163,plain,
% 3.97/0.97      ( ~ r2_hidden(X0,X1)
% 3.97/0.97      | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
% 3.97/0.97      | ~ r1_tarski(X1,k1_relset_1(sK2,sK3,sK4)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10768,plain,
% 3.97/0.97      ( ~ r2_hidden(sK1(sK4,sK5),X0)
% 3.97/0.97      | r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
% 3.97/0.97      | ~ r1_tarski(X0,k1_relset_1(sK2,sK3,sK4)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_6163]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10770,plain,
% 3.97/0.97      ( r2_hidden(sK1(sK4,sK5),k1_relset_1(sK2,sK3,sK4))
% 3.97/0.97      | ~ r2_hidden(sK1(sK4,sK5),k1_xboole_0)
% 3.97/0.97      | ~ r1_tarski(k1_xboole_0,k1_relset_1(sK2,sK3,sK4)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_10768]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10830,plain,
% 3.97/0.97      ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_9095,c_28,c_27,c_26,c_24,c_77,c_82,c_1640,c_1643,
% 3.97/0.97                 c_1761,c_1773,c_1834,c_3222,c_4894,c_5734,c_6220,c_7328,
% 3.97/0.97                 c_8118,c_8313,c_8471,c_8472,c_8812,c_8835,c_10770]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11102,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_7563,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,
% 3.97/0.97                 c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,
% 3.97/0.97                 c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8313,c_8471,
% 3.97/0.97                 c_8472,c_8812,c_8835,c_10770]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11119,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_11102]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11259,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),sK2) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_11119,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,
% 3.97/0.97                 c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,
% 3.97/0.97                 c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8313,c_8471,
% 3.97/0.97                 c_8472,c_8812,c_8835,c_10770]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11270,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(sK1(X0,sK5),X1) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,X1) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_11259,c_1454]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1441,plain,
% 3.97/0.97      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2457,plain,
% 3.97/0.97      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.97/0.97      inference(demodulation,[status(thm)],[c_2112,c_1441]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11283,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_11270,c_2457]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11462,plain,
% 3.97/0.97      ( r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_11283,c_29,c_30,c_31,c_24,c_33,c_23,c_38,c_77,c_78,
% 3.97/0.97                 c_82,c_1641,c_1644,c_1670,c_1797,c_1884,c_1885,c_2458,
% 3.97/0.97                 c_2596,c_3845,c_4078,c_4734,c_4862,c_5559,c_5605,c_5606,
% 3.97/0.97                 c_7256,c_7351,c_7385]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11463,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(X0,sK5)) = k1_funct_1(sK5,sK1(X0,sK5))
% 3.97/0.97      | r1_partfun1(X0,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_11462]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11478,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_4734,c_11463]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2874,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.97/0.97      | r1_partfun1(sK4,X0) = iProver_top
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1445,c_2457]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3783,plain,
% 3.97/0.97      ( v1_relat_1(X0) != iProver_top
% 3.97/0.97      | k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.97/0.97      | r1_partfun1(sK4,X0) = iProver_top
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_2874,c_29,c_30,c_1644]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3784,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.97/0.97      | r1_partfun1(sK4,X0) = iProver_top
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.97/0.97      inference(renaming,[status(thm)],[c_3783]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3797,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_3784]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3922,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.97/0.97      | sK3 = k1_xboole_0
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_3797,c_31,c_33,c_1641]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11499,plain,
% 3.97/0.97      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_11478,c_28,c_27,c_26,c_24,c_23,c_77,c_78,c_82,c_1640,
% 3.97/0.97                 c_1643,c_1761,c_1773,c_1797,c_1834,c_1884,c_1885,c_2596,
% 3.97/0.97                 c_3222,c_4894,c_5734,c_6220,c_7328,c_8118,c_8121,c_8313,
% 3.97/0.97                 c_8471,c_8472,c_8812,c_8835,c_10770]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1446,plain,
% 3.97/0.97      ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.97/0.97      | r1_partfun1(X1,X0) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 3.97/0.97      | v1_funct_1(X0) != iProver_top
% 3.97/0.97      | v1_funct_1(X1) != iProver_top
% 3.97/0.97      | v1_relat_1(X0) != iProver_top
% 3.97/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_11502,plain,
% 3.97/0.97      ( r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_11499,c_1446]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1774,plain,
% 3.97/0.97      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5))
% 3.97/0.97      | r1_partfun1(sK4,sK5) = iProver_top
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.97/0.97      | v1_funct_1(sK5) != iProver_top
% 3.97/0.97      | v1_funct_1(sK4) != iProver_top
% 3.97/0.97      | v1_relat_1(sK5) != iProver_top
% 3.97/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1773]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16394,plain,
% 3.97/0.97      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top ),
% 3.97/0.97      inference(global_propositional_subsumption,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_11502,c_28,c_29,c_27,c_30,c_26,c_31,c_24,c_33,c_23,
% 3.97/0.97                 c_38,c_77,c_78,c_82,c_1640,c_1641,c_1643,c_1644,c_1670,
% 3.97/0.97                 c_1761,c_1773,c_1774,c_1797,c_1834,c_1884,c_1885,c_2458,
% 3.97/0.97                 c_2596,c_3222,c_3845,c_4078,c_4734,c_4862,c_4894,c_5559,
% 3.97/0.97                 c_5605,c_5606,c_5734,c_6220,c_7328,c_7256,c_7351,c_7385,
% 3.97/0.97                 c_8118,c_8121,c_8313,c_8471,c_8472,c_8812,c_8835,
% 3.97/0.97                 c_10770]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16402,plain,
% 3.97/0.97      ( sK3 = k1_xboole_0
% 3.97/0.97      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_2182,c_16394]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(contradiction,plain,
% 3.97/0.97      ( $false ),
% 3.97/0.97      inference(minisat,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_16402,c_10830,c_4734,c_2596,c_1885,c_1884,c_1797,c_82,
% 3.97/0.97                 c_78,c_77,c_23]) ).
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  ------                               Statistics
% 3.97/0.97  
% 3.97/0.97  ------ General
% 3.97/0.97  
% 3.97/0.97  abstr_ref_over_cycles:                  0
% 3.97/0.97  abstr_ref_under_cycles:                 0
% 3.97/0.97  gc_basic_clause_elim:                   0
% 3.97/0.97  forced_gc_time:                         0
% 3.97/0.97  parsing_time:                           0.01
% 3.97/0.97  unif_index_cands_time:                  0.
% 3.97/0.97  unif_index_add_time:                    0.
% 3.97/0.97  orderings_time:                         0.
% 3.97/0.97  out_proof_time:                         0.015
% 3.97/0.97  total_time:                             0.412
% 3.97/0.97  num_of_symbols:                         51
% 3.97/0.97  num_of_terms:                           7319
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing
% 3.97/0.97  
% 3.97/0.97  num_of_splits:                          0
% 3.97/0.97  num_of_split_atoms:                     0
% 3.97/0.97  num_of_reused_defs:                     0
% 3.97/0.97  num_eq_ax_congr_red:                    18
% 3.97/0.97  num_of_sem_filtered_clauses:            1
% 3.97/0.97  num_of_subtypes:                        0
% 3.97/0.97  monotx_restored_types:                  0
% 3.97/0.97  sat_num_of_epr_types:                   0
% 3.97/0.97  sat_num_of_non_cyclic_types:            0
% 3.97/0.97  sat_guarded_non_collapsed_types:        0
% 3.97/0.97  num_pure_diseq_elim:                    0
% 3.97/0.97  simp_replaced_by:                       0
% 3.97/0.97  res_preprocessed:                       123
% 3.97/0.97  prep_upred:                             0
% 3.97/0.97  prep_unflattend:                        47
% 3.97/0.97  smt_new_axioms:                         0
% 3.97/0.97  pred_elim_cands:                        6
% 3.97/0.97  pred_elim:                              1
% 3.97/0.97  pred_elim_cl:                           4
% 3.97/0.97  pred_elim_cycles:                       3
% 3.97/0.97  merged_defs:                            0
% 3.97/0.97  merged_defs_ncl:                        0
% 3.97/0.97  bin_hyper_res:                          0
% 3.97/0.97  prep_cycles:                            4
% 3.97/0.97  pred_elim_time:                         0.012
% 3.97/0.97  splitting_time:                         0.
% 3.97/0.97  sem_filter_time:                        0.
% 3.97/0.97  monotx_time:                            0.001
% 3.97/0.97  subtype_inf_time:                       0.
% 3.97/0.97  
% 3.97/0.97  ------ Problem properties
% 3.97/0.97  
% 3.97/0.97  clauses:                                24
% 3.97/0.97  conjectures:                            8
% 3.97/0.97  epr:                                    7
% 3.97/0.97  horn:                                   19
% 3.97/0.97  ground:                                 10
% 3.97/0.97  unary:                                  6
% 3.97/0.97  binary:                                 9
% 3.97/0.97  lits:                                   65
% 3.97/0.97  lits_eq:                                15
% 3.97/0.97  fd_pure:                                0
% 3.97/0.97  fd_pseudo:                              0
% 3.97/0.97  fd_cond:                                0
% 3.97/0.97  fd_pseudo_cond:                         1
% 3.97/0.97  ac_symbols:                             0
% 3.97/0.97  
% 3.97/0.97  ------ Propositional Solver
% 3.97/0.97  
% 3.97/0.97  prop_solver_calls:                      31
% 3.97/0.97  prop_fast_solver_calls:                 1942
% 3.97/0.97  smt_solver_calls:                       0
% 3.97/0.97  smt_fast_solver_calls:                  0
% 3.97/0.97  prop_num_of_clauses:                    5281
% 3.97/0.97  prop_preprocess_simplified:             10497
% 3.97/0.97  prop_fo_subsumed:                       136
% 3.97/0.97  prop_solver_time:                       0.
% 3.97/0.97  smt_solver_time:                        0.
% 3.97/0.97  smt_fast_solver_time:                   0.
% 3.97/0.97  prop_fast_solver_time:                  0.
% 3.97/0.97  prop_unsat_core_time:                   0.
% 3.97/0.97  
% 3.97/0.97  ------ QBF
% 3.97/0.97  
% 3.97/0.97  qbf_q_res:                              0
% 3.97/0.97  qbf_num_tautologies:                    0
% 3.97/0.97  qbf_prep_cycles:                        0
% 3.97/0.97  
% 3.97/0.97  ------ BMC1
% 3.97/0.97  
% 3.97/0.97  bmc1_current_bound:                     -1
% 3.97/0.97  bmc1_last_solved_bound:                 -1
% 3.97/0.97  bmc1_unsat_core_size:                   -1
% 3.97/0.97  bmc1_unsat_core_parents_size:           -1
% 3.97/0.97  bmc1_merge_next_fun:                    0
% 3.97/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation
% 3.97/0.97  
% 3.97/0.97  inst_num_of_clauses:                    1657
% 3.97/0.97  inst_num_in_passive:                    576
% 3.97/0.97  inst_num_in_active:                     629
% 3.97/0.97  inst_num_in_unprocessed:                452
% 3.97/0.97  inst_num_of_loops:                      930
% 3.97/0.97  inst_num_of_learning_restarts:          0
% 3.97/0.97  inst_num_moves_active_passive:          294
% 3.97/0.97  inst_lit_activity:                      0
% 3.97/0.97  inst_lit_activity_moves:                0
% 3.97/0.97  inst_num_tautologies:                   0
% 3.97/0.97  inst_num_prop_implied:                  0
% 3.97/0.97  inst_num_existing_simplified:           0
% 3.97/0.97  inst_num_eq_res_simplified:             0
% 3.97/0.97  inst_num_child_elim:                    0
% 3.97/0.97  inst_num_of_dismatching_blockings:      409
% 3.97/0.97  inst_num_of_non_proper_insts:           1756
% 3.97/0.97  inst_num_of_duplicates:                 0
% 3.97/0.97  inst_inst_num_from_inst_to_res:         0
% 3.97/0.97  inst_dismatching_checking_time:         0.
% 3.97/0.97  
% 3.97/0.97  ------ Resolution
% 3.97/0.97  
% 3.97/0.97  res_num_of_clauses:                     0
% 3.97/0.97  res_num_in_passive:                     0
% 3.97/0.97  res_num_in_active:                      0
% 3.97/0.97  res_num_of_loops:                       127
% 3.97/0.97  res_forward_subset_subsumed:            126
% 3.97/0.97  res_backward_subset_subsumed:           6
% 3.97/0.97  res_forward_subsumed:                   0
% 3.97/0.97  res_backward_subsumed:                  0
% 3.97/0.97  res_forward_subsumption_resolution:     0
% 3.97/0.97  res_backward_subsumption_resolution:    0
% 3.97/0.97  res_clause_to_clause_subsumption:       3224
% 3.97/0.97  res_orphan_elimination:                 0
% 3.97/0.97  res_tautology_del:                      200
% 3.97/0.97  res_num_eq_res_simplified:              0
% 3.97/0.97  res_num_sel_changes:                    0
% 3.97/0.97  res_moves_from_active_to_pass:          0
% 3.97/0.97  
% 3.97/0.97  ------ Superposition
% 3.97/0.97  
% 3.97/0.97  sup_time_total:                         0.
% 3.97/0.97  sup_time_generating:                    0.
% 3.97/0.97  sup_time_sim_full:                      0.
% 3.97/0.97  sup_time_sim_immed:                     0.
% 3.97/0.97  
% 3.97/0.97  sup_num_of_clauses:                     304
% 3.97/0.97  sup_num_in_active:                      168
% 3.97/0.97  sup_num_in_passive:                     136
% 3.97/0.97  sup_num_of_loops:                       185
% 3.97/0.97  sup_fw_superposition:                   430
% 3.97/0.97  sup_bw_superposition:                   255
% 3.97/0.97  sup_immediate_simplified:               222
% 3.97/0.97  sup_given_eliminated:                   2
% 3.97/0.97  comparisons_done:                       0
% 3.97/0.97  comparisons_avoided:                    74
% 3.97/0.97  
% 3.97/0.97  ------ Simplifications
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  sim_fw_subset_subsumed:                 136
% 3.97/0.97  sim_bw_subset_subsumed:                 36
% 3.97/0.97  sim_fw_subsumed:                        44
% 3.97/0.97  sim_bw_subsumed:                        42
% 3.97/0.97  sim_fw_subsumption_res:                 1
% 3.97/0.97  sim_bw_subsumption_res:                 0
% 3.97/0.97  sim_tautology_del:                      21
% 3.97/0.97  sim_eq_tautology_del:                   42
% 3.97/0.97  sim_eq_res_simp:                        0
% 3.97/0.97  sim_fw_demodulated:                     3
% 3.97/0.97  sim_bw_demodulated:                     3
% 3.97/0.97  sim_light_normalised:                   4
% 3.97/0.97  sim_joinable_taut:                      0
% 3.97/0.97  sim_joinable_simp:                      0
% 3.97/0.97  sim_ac_normalised:                      0
% 3.97/0.97  sim_smt_subsumption:                    0
% 3.97/0.97  
%------------------------------------------------------------------------------
