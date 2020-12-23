%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:51 EST 2020

% Result     : Theorem 23.76s
% Output     : CNFRefutation 23.76s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5180)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK7,sK6,sK8))
          | ~ m1_subset_1(X3,sK7) )
      & k1_xboole_0 != k2_relset_1(sK7,sK6,sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK7,sK6,sK8))
        | ~ m1_subset_1(X3,sK7) )
    & k1_xboole_0 != k2_relset_1(sK7,sK6,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f49])).

fof(f75,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK7,sK6,sK8))
      | ~ m1_subset_1(X3,sK7) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f47])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    k1_xboole_0 != k2_relset_1(sK7,sK6,sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

cnf(c_1077,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1076,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_94496,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1077,c_1076])).

cnf(c_15,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_90889,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK7,sK6)) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_92790,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK6))
    | ~ r2_hidden(X0,sK8) ),
    inference(resolution,[status(thm)],[c_2,c_90889])).

cnf(c_93375,plain,
    ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK7,sK6)))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
    inference(resolution,[status(thm)],[c_16,c_92790])).

cnf(c_98828,plain,
    ( r2_hidden(sK1(sK8,X0),X0)
    | r2_hidden(sK1(sK8,X0),k1_relat_1(k2_zfmisc_1(sK7,sK6)))
    | k1_relat_1(sK8) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_93375])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,k1_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_99012,plain,
    ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
    | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),k1_relat_1(k2_zfmisc_1(sK7,sK6)))
    | k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
    inference(resolution,[status(thm)],[c_98828,c_24])).

cnf(c_4464,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_15,c_16])).

cnf(c_11202,plain,
    ( ~ m1_subset_1(sK1(X0,k1_relset_1(sK7,sK6,sK8)),sK7)
    | r2_hidden(sK1(X0,k1_relset_1(sK7,sK6,sK8)),k1_relat_1(X0))
    | k1_relat_1(X0) = k1_relset_1(sK7,sK6,sK8) ),
    inference(resolution,[status(thm)],[c_4464,c_24])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_8573,plain,
    ( r1_tarski(k1_relat_1(sK8),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_324,c_26])).

cnf(c_1626,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1772,plain,
    ( r1_tarski(k1_relat_1(sK8),sK7) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1624])).

cnf(c_1773,plain,
    ( r1_tarski(k1_relat_1(sK8),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1772])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_196])).

cnf(c_1943,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK7,sK6)) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_5300,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK7,sK6))
    | v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_242,c_1943])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5567,plain,
    ( v1_relat_1(sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5300,c_18])).

cnf(c_9002,plain,
    ( r1_tarski(k1_relat_1(sK8),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8573,c_1773,c_5567])).

cnf(c_9016,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_9002,c_2])).

cnf(c_11421,plain,
    ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
    | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
    | k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
    inference(resolution,[status(thm)],[c_11202,c_9016])).

cnf(c_2805,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1077,c_1076])).

cnf(c_11439,plain,
    ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
    | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
    | k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_11421,c_2805])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1756,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_12917,plain,
    ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11439,c_26,c_1756])).

cnf(c_12923,plain,
    ( k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
    inference(resolution,[status(thm)],[c_12917,c_2805])).

cnf(c_99284,plain,
    ( k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_99012,c_12923])).

cnf(c_100771,plain,
    ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_94496,c_99284])).

cnf(c_1078,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_100923,plain,
    ( r1_tarski(X0,k1_relset_1(sK7,sK6,sK8))
    | ~ r1_tarski(X1,k1_relat_1(sK8))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_100771,c_1078])).

cnf(c_101297,plain,
    ( ~ r1_tarski(k1_relset_1(sK7,sK6,sK8),k1_relat_1(sK8))
    | r1_tarski(k1_relat_1(sK8),k1_relset_1(sK7,sK6,sK8)) ),
    inference(resolution,[status(thm)],[c_100923,c_99284])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_91154,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_99292,plain,
    ( ~ r1_tarski(X0,k1_relset_1(sK7,sK6,sK8))
    | r1_tarski(X1,k1_relat_1(sK8))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_99284,c_1078])).

cnf(c_99869,plain,
    ( r1_tarski(X0,k1_relat_1(sK8))
    | X0 != k1_relset_1(sK7,sK6,sK8) ),
    inference(resolution,[status(thm)],[c_91154,c_99292])).

cnf(c_100138,plain,
    ( r1_tarski(k1_relset_1(sK7,sK6,sK8),k1_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_99869,c_1076])).

cnf(c_101308,plain,
    ( r1_tarski(k1_relat_1(sK8),k1_relset_1(sK7,sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_101297,c_100138])).

cnf(c_101321,plain,
    ( r2_hidden(X0,k1_relset_1(sK7,sK6,sK8))
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_101308,c_2])).

cnf(c_101465,plain,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_101321,c_24])).

cnf(c_19,plain,
    ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_94470,plain,
    ( r2_hidden(sK4(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_101487,plain,
    ( ~ m1_subset_1(sK4(sK8),sK7)
    | ~ v1_relat_1(sK8)
    | k1_xboole_0 = sK8 ),
    inference(resolution,[status(thm)],[c_101465,c_94470])).

cnf(c_1631,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1634,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2916,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_1634])).

cnf(c_1629,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2460,plain,
    ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1626,c_1629])).

cnf(c_1627,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK7,sK6,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3665,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_1627])).

cnf(c_5177,plain,
    ( sK8 = k1_xboole_0
    | m1_subset_1(sK4(sK8),sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_3665])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK7,sK6,sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_77,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_78,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1082,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1091,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1703,plain,
    ( ~ r1_tarski(k2_relset_1(sK7,sK6,sK8),k1_xboole_0)
    | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1760,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | k2_relset_1(sK7,sK6,sK8) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relset_1(sK7,sK6,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1840,plain,
    ( X0 != X1
    | k2_relset_1(sK7,sK6,sK8) != X1
    | k2_relset_1(sK7,sK6,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_2022,plain,
    ( X0 != k2_relat_1(sK8)
    | k2_relset_1(sK7,sK6,sK8) = X0
    | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_2329,plain,
    ( k2_relset_1(X0,X1,sK8) != k2_relat_1(sK8)
    | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(X0,X1,sK8)
    | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_2331,plain,
    ( k2_relset_1(sK7,sK6,sK8) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
    | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_2330,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2333,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2330])).

cnf(c_1081,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1763,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_1913,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_2875,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_2877,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2875])).

cnf(c_3344,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_3345,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3344])).

cnf(c_5568,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5567])).

cnf(c_1906,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_2182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
    | k2_relset_1(sK7,sK6,sK8) != X0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_10030,plain,
    ( ~ m1_subset_1(k2_relset_1(X0,X1,sK8),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
    | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X0,X1,sK8)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_10043,plain,
    ( m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k2_relset_1(k1_xboole_0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
    | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10030])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38597,plain,
    ( m1_subset_1(k2_relset_1(X0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_38601,plain,
    ( m1_subset_1(k2_relset_1(k1_xboole_0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_38597])).

cnf(c_49909,plain,
    ( m1_subset_1(sK4(sK8),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5177,c_26,c_25,c_72,c_77,c_78,c_83,c_1091,c_1703,c_1760,c_1797,c_2331,c_2333,c_2877,c_3345,c_5568,c_10043,c_38601])).

cnf(c_49911,plain,
    ( ~ m1_subset_1(sK4(sK8),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49909])).

cnf(c_101596,plain,
    ( ~ m1_subset_1(sK4(sK8),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_101487,c_26,c_25,c_72,c_77,c_78,c_83,c_1091,c_1703,c_1760,c_1797,c_2331,c_2333,c_2877,c_3345,c_5180,c_5567,c_10043,c_38601])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_101608,plain,
    ( ~ r2_hidden(sK4(sK8),sK7) ),
    inference(resolution,[status(thm)],[c_101596,c_8])).

cnf(c_3726,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1078,c_1076])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7502,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_3726,c_5])).

cnf(c_27171,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7502,c_3])).

cnf(c_6493,plain,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2805,c_5])).

cnf(c_3718,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k1_relset_1(X1,X2,X0))
    | ~ r1_tarski(X4,k1_relat_1(X0))
    | X3 != X4 ),
    inference(resolution,[status(thm)],[c_1078,c_22])).

cnf(c_2775,plain,
    ( r2_hidden(sK4(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_9219,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | ~ v1_relat_1(sK8)
    | k1_xboole_0 = sK8 ),
    inference(resolution,[status(thm)],[c_9016,c_2775])).

cnf(c_9249,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | k1_xboole_0 = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9219,c_5567])).

cnf(c_3786,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1081,c_1076])).

cnf(c_9461,plain,
    ( ~ m1_subset_1(sK8,X0)
    | m1_subset_1(k1_xboole_0,X0)
    | r2_hidden(sK4(sK8),sK7) ),
    inference(resolution,[status(thm)],[c_9249,c_3786])).

cnf(c_10646,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    | r2_hidden(sK4(sK8),sK7) ),
    inference(resolution,[status(thm)],[c_9461,c_26])).

cnf(c_15119,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | r1_tarski(X0,k1_relset_1(sK7,sK6,k1_xboole_0))
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_3718,c_10646])).

cnf(c_23843,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | ~ r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_relset_1(sK7,sK6,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6493,c_15119])).

cnf(c_27377,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | r1_tarski(k1_xboole_0,k1_relset_1(sK7,sK6,k1_xboole_0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_27171,c_23843])).

cnf(c_1747,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1749,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_1745,plain,
    ( k2_relset_1(sK7,sK6,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_1841,plain,
    ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X0,X1,X2)
    | k1_xboole_0 != k2_relset_1(X0,X1,X2)
    | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_1843,plain,
    ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8)
    | k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_1860,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1864,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_1641,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1628,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2202,plain,
    ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1628])).

cnf(c_2454,plain,
    ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_2202])).

cnf(c_3961,plain,
    ( k2_relset_1(X0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1641,c_2454])).

cnf(c_1630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4043,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3961,c_1630])).

cnf(c_1748,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1747])).

cnf(c_1750,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_1863,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_1865,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_4045,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4043])).

cnf(c_5548,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4043,c_1750,c_1865,c_4045])).

cnf(c_1637,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5552,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5548,c_1637])).

cnf(c_5559,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5552])).

cnf(c_2801,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_1077,c_4])).

cnf(c_7828,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | k1_xboole_0 = k2_relset_1(X1,X2,X0) ),
    inference(resolution,[status(thm)],[c_2801,c_23])).

cnf(c_7830,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7828])).

cnf(c_9455,plain,
    ( r2_hidden(sK4(sK8),sK7)
    | sK8 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9249,c_2805])).

cnf(c_10071,plain,
    ( X0 != k2_relset_1(X1,X2,sK8)
    | k2_relset_1(sK7,sK6,sK8) = X0
    | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X1,X2,sK8) ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_34128,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(X3,X4,sK8)
    | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(X0,X1,X2)
    | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X3,X4,sK8) ),
    inference(instantiation,[status(thm)],[c_10071])).

cnf(c_34130,plain,
    ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
    | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_34128])).

cnf(c_1085,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k2_relset_1(X0,X2,X4) = k2_relset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_34129,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != sK8
    | k2_relset_1(X0,X2,X4) = k2_relset_1(X1,X3,sK8) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_34131,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
    | k1_xboole_0 != sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34129])).

cnf(c_34258,plain,
    ( r2_hidden(sK4(sK8),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27377,c_26,c_25,c_72,c_77,c_78,c_83,c_1749,c_1760,c_1843,c_1864,c_2331,c_2333,c_2877,c_3345,c_5559,c_7830,c_9249,c_9455,c_34130,c_34131])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_101608,c_34258])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:19:23 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 23.76/3.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.76/3.47  
% 23.76/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.76/3.47  
% 23.76/3.47  ------  iProver source info
% 23.76/3.47  
% 23.76/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.76/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.76/3.47  git: non_committed_changes: false
% 23.76/3.47  git: last_make_outside_of_git: false
% 23.76/3.47  
% 23.76/3.47  ------ 
% 23.76/3.47  ------ Parsing...
% 23.76/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.76/3.47  
% 23.76/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.76/3.47  
% 23.76/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.76/3.47  
% 23.76/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.76/3.47  ------ Proving...
% 23.76/3.47  ------ Problem Properties 
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  clauses                                 25
% 23.76/3.47  conjectures                             3
% 23.76/3.47  EPR                                     5
% 23.76/3.47  Horn                                    21
% 23.76/3.47  unary                                   6
% 23.76/3.47  binary                                  12
% 23.76/3.47  lits                                    51
% 23.76/3.47  lits eq                                 12
% 23.76/3.47  fd_pure                                 0
% 23.76/3.47  fd_pseudo                               0
% 23.76/3.47  fd_cond                                 3
% 23.76/3.47  fd_pseudo_cond                          2
% 23.76/3.47  AC symbols                              0
% 23.76/3.47  
% 23.76/3.47  ------ Input Options Time Limit: Unbounded
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  ------ 
% 23.76/3.47  Current options:
% 23.76/3.47  ------ 
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  ------ Proving...
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  % SZS status Theorem for theBenchmark.p
% 23.76/3.47  
% 23.76/3.47  % SZS output start CNFRefutation for theBenchmark.p
% 23.76/3.47  
% 23.76/3.47  fof(f9,axiom,(
% 23.76/3.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f41,plain,(
% 23.76/3.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 23.76/3.47    inference(nnf_transformation,[],[f9])).
% 23.76/3.47  
% 23.76/3.47  fof(f42,plain,(
% 23.76/3.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 23.76/3.47    inference(rectify,[],[f41])).
% 23.76/3.47  
% 23.76/3.47  fof(f45,plain,(
% 23.76/3.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f44,plain,(
% 23.76/3.47    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f43,plain,(
% 23.76/3.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f46,plain,(
% 23.76/3.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 23.76/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).
% 23.76/3.47  
% 23.76/3.47  fof(f67,plain,(
% 23.76/3.47    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f46])).
% 23.76/3.47  
% 23.76/3.47  fof(f66,plain,(
% 23.76/3.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 23.76/3.47    inference(cnf_transformation,[],[f46])).
% 23.76/3.47  
% 23.76/3.47  fof(f80,plain,(
% 23.76/3.47    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 23.76/3.47    inference(equality_resolution,[],[f66])).
% 23.76/3.47  
% 23.76/3.47  fof(f1,axiom,(
% 23.76/3.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f20,plain,(
% 23.76/3.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.76/3.47    inference(ennf_transformation,[],[f1])).
% 23.76/3.47  
% 23.76/3.47  fof(f33,plain,(
% 23.76/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.76/3.47    inference(nnf_transformation,[],[f20])).
% 23.76/3.47  
% 23.76/3.47  fof(f34,plain,(
% 23.76/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.76/3.47    inference(rectify,[],[f33])).
% 23.76/3.47  
% 23.76/3.47  fof(f35,plain,(
% 23.76/3.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f36,plain,(
% 23.76/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.76/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 23.76/3.47  
% 23.76/3.47  fof(f51,plain,(
% 23.76/3.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f36])).
% 23.76/3.47  
% 23.76/3.47  fof(f6,axiom,(
% 23.76/3.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f39,plain,(
% 23.76/3.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.76/3.47    inference(nnf_transformation,[],[f6])).
% 23.76/3.47  
% 23.76/3.47  fof(f60,plain,(
% 23.76/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f39])).
% 23.76/3.47  
% 23.76/3.47  fof(f16,conjecture,(
% 23.76/3.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f17,negated_conjecture,(
% 23.76/3.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 23.76/3.47    inference(negated_conjecture,[],[f16])).
% 23.76/3.47  
% 23.76/3.47  fof(f18,plain,(
% 23.76/3.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 23.76/3.47    inference(pure_predicate_removal,[],[f17])).
% 23.76/3.47  
% 23.76/3.47  fof(f31,plain,(
% 23.76/3.47    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 23.76/3.47    inference(ennf_transformation,[],[f18])).
% 23.76/3.47  
% 23.76/3.47  fof(f32,plain,(
% 23.76/3.47    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 23.76/3.47    inference(flattening,[],[f31])).
% 23.76/3.47  
% 23.76/3.47  fof(f49,plain,(
% 23.76/3.47    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK7,sK6,sK8)) | ~m1_subset_1(X3,sK7)) & k1_xboole_0 != k2_relset_1(sK7,sK6,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))))),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f50,plain,(
% 23.76/3.47    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK7,sK6,sK8)) | ~m1_subset_1(X3,sK7)) & k1_xboole_0 != k2_relset_1(sK7,sK6,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))),
% 23.76/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f49])).
% 23.76/3.47  
% 23.76/3.47  fof(f75,plain,(
% 23.76/3.47    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))),
% 23.76/3.47    inference(cnf_transformation,[],[f50])).
% 23.76/3.47  
% 23.76/3.47  fof(f77,plain,(
% 23.76/3.47    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK7,sK6,sK8)) | ~m1_subset_1(X3,sK7)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f50])).
% 23.76/3.47  
% 23.76/3.47  fof(f12,axiom,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f19,plain,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.76/3.47    inference(pure_predicate_removal,[],[f12])).
% 23.76/3.47  
% 23.76/3.47  fof(f27,plain,(
% 23.76/3.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.76/3.47    inference(ennf_transformation,[],[f19])).
% 23.76/3.47  
% 23.76/3.47  fof(f71,plain,(
% 23.76/3.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f27])).
% 23.76/3.47  
% 23.76/3.47  fof(f8,axiom,(
% 23.76/3.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f24,plain,(
% 23.76/3.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.76/3.47    inference(ennf_transformation,[],[f8])).
% 23.76/3.47  
% 23.76/3.47  fof(f40,plain,(
% 23.76/3.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.76/3.47    inference(nnf_transformation,[],[f24])).
% 23.76/3.47  
% 23.76/3.47  fof(f63,plain,(
% 23.76/3.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f40])).
% 23.76/3.47  
% 23.76/3.47  fof(f7,axiom,(
% 23.76/3.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f23,plain,(
% 23.76/3.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.76/3.47    inference(ennf_transformation,[],[f7])).
% 23.76/3.47  
% 23.76/3.47  fof(f62,plain,(
% 23.76/3.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f23])).
% 23.76/3.47  
% 23.76/3.47  fof(f61,plain,(
% 23.76/3.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f39])).
% 23.76/3.47  
% 23.76/3.47  fof(f10,axiom,(
% 23.76/3.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f69,plain,(
% 23.76/3.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f10])).
% 23.76/3.47  
% 23.76/3.47  fof(f14,axiom,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f29,plain,(
% 23.76/3.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.76/3.47    inference(ennf_transformation,[],[f14])).
% 23.76/3.47  
% 23.76/3.47  fof(f73,plain,(
% 23.76/3.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f29])).
% 23.76/3.47  
% 23.76/3.47  fof(f53,plain,(
% 23.76/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f36])).
% 23.76/3.47  
% 23.76/3.47  fof(f52,plain,(
% 23.76/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f36])).
% 23.76/3.47  
% 23.76/3.47  fof(f11,axiom,(
% 23.76/3.47    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f25,plain,(
% 23.76/3.47    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 23.76/3.47    inference(ennf_transformation,[],[f11])).
% 23.76/3.47  
% 23.76/3.47  fof(f26,plain,(
% 23.76/3.47    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 23.76/3.47    inference(flattening,[],[f25])).
% 23.76/3.47  
% 23.76/3.47  fof(f47,plain,(
% 23.76/3.47    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))),
% 23.76/3.47    introduced(choice_axiom,[])).
% 23.76/3.47  
% 23.76/3.47  fof(f48,plain,(
% 23.76/3.47    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0))),
% 23.76/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f47])).
% 23.76/3.47  
% 23.76/3.47  fof(f70,plain,(
% 23.76/3.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f48])).
% 23.76/3.47  
% 23.76/3.47  fof(f76,plain,(
% 23.76/3.47    k1_xboole_0 != k2_relset_1(sK7,sK6,sK8)),
% 23.76/3.47    inference(cnf_transformation,[],[f50])).
% 23.76/3.47  
% 23.76/3.47  fof(f4,axiom,(
% 23.76/3.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f37,plain,(
% 23.76/3.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.76/3.47    inference(nnf_transformation,[],[f4])).
% 23.76/3.47  
% 23.76/3.47  fof(f38,plain,(
% 23.76/3.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.76/3.47    inference(flattening,[],[f37])).
% 23.76/3.47  
% 23.76/3.47  fof(f56,plain,(
% 23.76/3.47    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f38])).
% 23.76/3.47  
% 23.76/3.47  fof(f57,plain,(
% 23.76/3.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 23.76/3.47    inference(cnf_transformation,[],[f38])).
% 23.76/3.47  
% 23.76/3.47  fof(f79,plain,(
% 23.76/3.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 23.76/3.47    inference(equality_resolution,[],[f57])).
% 23.76/3.47  
% 23.76/3.47  fof(f2,axiom,(
% 23.76/3.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f54,plain,(
% 23.76/3.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f2])).
% 23.76/3.47  
% 23.76/3.47  fof(f3,axiom,(
% 23.76/3.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f21,plain,(
% 23.76/3.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 23.76/3.47    inference(ennf_transformation,[],[f3])).
% 23.76/3.47  
% 23.76/3.47  fof(f55,plain,(
% 23.76/3.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f21])).
% 23.76/3.47  
% 23.76/3.47  fof(f15,axiom,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f30,plain,(
% 23.76/3.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.76/3.47    inference(ennf_transformation,[],[f15])).
% 23.76/3.47  
% 23.76/3.47  fof(f74,plain,(
% 23.76/3.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f30])).
% 23.76/3.47  
% 23.76/3.47  fof(f13,axiom,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f28,plain,(
% 23.76/3.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.76/3.47    inference(ennf_transformation,[],[f13])).
% 23.76/3.47  
% 23.76/3.47  fof(f72,plain,(
% 23.76/3.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.76/3.47    inference(cnf_transformation,[],[f28])).
% 23.76/3.47  
% 23.76/3.47  fof(f5,axiom,(
% 23.76/3.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 23.76/3.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.76/3.47  
% 23.76/3.47  fof(f22,plain,(
% 23.76/3.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 23.76/3.47    inference(ennf_transformation,[],[f5])).
% 23.76/3.47  
% 23.76/3.47  fof(f59,plain,(
% 23.76/3.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 23.76/3.47    inference(cnf_transformation,[],[f22])).
% 23.76/3.47  
% 23.76/3.47  fof(f58,plain,(
% 23.76/3.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 23.76/3.47    inference(cnf_transformation,[],[f38])).
% 23.76/3.47  
% 23.76/3.47  fof(f78,plain,(
% 23.76/3.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 23.76/3.47    inference(equality_resolution,[],[f58])).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1077,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1076,plain,( X0 = X0 ),theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_94496,plain,
% 23.76/3.47      ( X0 != X1 | X1 = X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1077,c_1076]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_15,plain,
% 23.76/3.47      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 23.76/3.47      | r2_hidden(sK1(X0,X1),X1)
% 23.76/3.47      | k1_relat_1(X0) = X1 ),
% 23.76/3.47      inference(cnf_transformation,[],[f67]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_16,plain,
% 23.76/3.47      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f80]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2,plain,
% 23.76/3.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.76/3.47      inference(cnf_transformation,[],[f51]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_10,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f60]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_26,negated_conjecture,
% 23.76/3.47      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
% 23.76/3.47      inference(cnf_transformation,[],[f75]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_90889,plain,
% 23.76/3.47      ( r1_tarski(sK8,k2_zfmisc_1(sK7,sK6)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_10,c_26]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_92790,plain,
% 23.76/3.47      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK6)) | ~ r2_hidden(X0,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_2,c_90889]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_93375,plain,
% 23.76/3.47      ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_16,c_92790]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_98828,plain,
% 23.76/3.47      ( r2_hidden(sK1(sK8,X0),X0)
% 23.76/3.47      | r2_hidden(sK1(sK8,X0),k1_relat_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | k1_relat_1(sK8) = X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_15,c_93375]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_24,negated_conjecture,
% 23.76/3.47      ( ~ m1_subset_1(X0,sK7)
% 23.76/3.47      | ~ r2_hidden(X0,k1_relset_1(sK7,sK6,sK8)) ),
% 23.76/3.47      inference(cnf_transformation,[],[f77]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_99012,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),k1_relat_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_98828,c_24]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_4464,plain,
% 23.76/3.47      ( r2_hidden(sK1(X0,X1),X1)
% 23.76/3.47      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 23.76/3.47      | k1_relat_1(X0) = X1 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_15,c_16]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_11202,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK1(X0,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | r2_hidden(sK1(X0,k1_relset_1(sK7,sK6,sK8)),k1_relat_1(X0))
% 23.76/3.47      | k1_relat_1(X0) = k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_4464,c_24]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_20,plain,
% 23.76/3.47      ( v4_relat_1(X0,X1)
% 23.76/3.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.76/3.47      inference(cnf_transformation,[],[f71]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_13,plain,
% 23.76/3.47      ( ~ v4_relat_1(X0,X1)
% 23.76/3.47      | r1_tarski(k1_relat_1(X0),X1)
% 23.76/3.47      | ~ v1_relat_1(X0) ),
% 23.76/3.47      inference(cnf_transformation,[],[f63]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_324,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | r1_tarski(k1_relat_1(X0),X1)
% 23.76/3.47      | ~ v1_relat_1(X0) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_8573,plain,
% 23.76/3.47      ( r1_tarski(k1_relat_1(sK8),sK7) | ~ v1_relat_1(sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_324,c_26]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1626,plain,
% 23.76/3.47      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1624,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.76/3.47      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 23.76/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1772,plain,
% 23.76/3.47      ( r1_tarski(k1_relat_1(sK8),sK7) = iProver_top
% 23.76/3.47      | v1_relat_1(sK8) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_1626,c_1624]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1773,plain,
% 23.76/3.47      ( r1_tarski(k1_relat_1(sK8),sK7) | ~ v1_relat_1(sK8) ),
% 23.76/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_1772]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_11,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.76/3.47      | ~ v1_relat_1(X1)
% 23.76/3.47      | v1_relat_1(X0) ),
% 23.76/3.47      inference(cnf_transformation,[],[f62]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f61]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_195,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.76/3.47      inference(prop_impl,[status(thm)],[c_9]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_196,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.76/3.47      inference(renaming,[status(thm)],[c_195]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_242,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.76/3.47      inference(bin_hyper_res,[status(thm)],[c_11,c_196]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1943,plain,
% 23.76/3.47      ( r1_tarski(sK8,k2_zfmisc_1(sK7,sK6)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_10,c_26]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5300,plain,
% 23.76/3.47      ( ~ v1_relat_1(k2_zfmisc_1(sK7,sK6)) | v1_relat_1(sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_242,c_1943]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_18,plain,
% 23.76/3.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.76/3.47      inference(cnf_transformation,[],[f69]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5567,plain,
% 23.76/3.47      ( v1_relat_1(sK8) ),
% 23.76/3.47      inference(forward_subsumption_resolution,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_5300,c_18]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9002,plain,
% 23.76/3.47      ( r1_tarski(k1_relat_1(sK8),sK7) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_8573,c_1773,c_5567]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9016,plain,
% 23.76/3.47      ( ~ r2_hidden(X0,k1_relat_1(sK8)) | r2_hidden(X0,sK7) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_9002,c_2]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_11421,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_11202,c_9016]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2805,plain,
% 23.76/3.47      ( X0 != X1 | X1 = X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1077,c_1076]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_11439,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | r2_hidden(sK1(sK8,k1_relset_1(sK7,sK6,sK8)),sK7)
% 23.76/3.47      | k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_11421,c_2805]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_22,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.76/3.47      inference(cnf_transformation,[],[f73]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1756,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_22]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_12917,plain,
% 23.76/3.47      ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_11439,c_26,c_1756]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_12923,plain,
% 23.76/3.47      ( k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_12917,c_2805]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_99284,plain,
% 23.76/3.47      ( k1_relat_1(sK8) = k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_99012,c_12923]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_100771,plain,
% 23.76/3.47      ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_94496,c_99284]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1078,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.76/3.47      theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_100923,plain,
% 23.76/3.47      ( r1_tarski(X0,k1_relset_1(sK7,sK6,sK8))
% 23.76/3.47      | ~ r1_tarski(X1,k1_relat_1(sK8))
% 23.76/3.47      | X0 != X1 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_100771,c_1078]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101297,plain,
% 23.76/3.47      ( ~ r1_tarski(k1_relset_1(sK7,sK6,sK8),k1_relat_1(sK8))
% 23.76/3.47      | r1_tarski(k1_relat_1(sK8),k1_relset_1(sK7,sK6,sK8)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_100923,c_99284]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_0,plain,
% 23.76/3.47      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f53]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1,plain,
% 23.76/3.47      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f52]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_91154,plain,
% 23.76/3.47      ( r1_tarski(X0,X0) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_99292,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,k1_relset_1(sK7,sK6,sK8))
% 23.76/3.47      | r1_tarski(X1,k1_relat_1(sK8))
% 23.76/3.47      | X1 != X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_99284,c_1078]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_99869,plain,
% 23.76/3.47      ( r1_tarski(X0,k1_relat_1(sK8)) | X0 != k1_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_91154,c_99292]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_100138,plain,
% 23.76/3.47      ( r1_tarski(k1_relset_1(sK7,sK6,sK8),k1_relat_1(sK8)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_99869,c_1076]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101308,plain,
% 23.76/3.47      ( r1_tarski(k1_relat_1(sK8),k1_relset_1(sK7,sK6,sK8)) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_101297,c_100138]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101321,plain,
% 23.76/3.47      ( r2_hidden(X0,k1_relset_1(sK7,sK6,sK8))
% 23.76/3.47      | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_101308,c_2]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101465,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,sK7) | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_101321,c_24]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_19,plain,
% 23.76/3.47      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
% 23.76/3.47      | ~ v1_relat_1(X0)
% 23.76/3.47      | k1_xboole_0 = X0 ),
% 23.76/3.47      inference(cnf_transformation,[],[f70]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_94470,plain,
% 23.76/3.47      ( r2_hidden(sK4(X0),k1_relat_1(X0))
% 23.76/3.47      | ~ v1_relat_1(X0)
% 23.76/3.47      | k1_xboole_0 = X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101487,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK4(sK8),sK7)
% 23.76/3.47      | ~ v1_relat_1(sK8)
% 23.76/3.47      | k1_xboole_0 = sK8 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_101465,c_94470]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1631,plain,
% 23.76/3.47      ( k1_xboole_0 = X0
% 23.76/3.47      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) = iProver_top
% 23.76/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1634,plain,
% 23.76/3.47      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 23.76/3.47      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2916,plain,
% 23.76/3.47      ( k1_xboole_0 = X0
% 23.76/3.47      | r2_hidden(sK4(X0),k1_relat_1(X0)) = iProver_top
% 23.76/3.47      | v1_relat_1(X0) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_1631,c_1634]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1629,plain,
% 23.76/3.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.76/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2460,plain,
% 23.76/3.47      ( k1_relset_1(sK7,sK6,sK8) = k1_relat_1(sK8) ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_1626,c_1629]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1627,plain,
% 23.76/3.47      ( m1_subset_1(X0,sK7) != iProver_top
% 23.76/3.47      | r2_hidden(X0,k1_relset_1(sK7,sK6,sK8)) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3665,plain,
% 23.76/3.47      ( m1_subset_1(X0,sK7) != iProver_top
% 23.76/3.47      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_2460,c_1627]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5177,plain,
% 23.76/3.47      ( sK8 = k1_xboole_0
% 23.76/3.47      | m1_subset_1(sK4(sK8),sK7) != iProver_top
% 23.76/3.47      | v1_relat_1(sK8) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_2916,c_3665]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_25,negated_conjecture,
% 23.76/3.47      ( k1_xboole_0 != k2_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(cnf_transformation,[],[f76]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_72,plain,
% 23.76/3.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_9]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_7,plain,
% 23.76/3.47      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 23.76/3.47      | k1_xboole_0 = X0
% 23.76/3.47      | k1_xboole_0 = X1 ),
% 23.76/3.47      inference(cnf_transformation,[],[f56]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_77,plain,
% 23.76/3.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.76/3.47      | k1_xboole_0 = k1_xboole_0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_7]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_6,plain,
% 23.76/3.47      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.76/3.47      inference(cnf_transformation,[],[f79]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_78,plain,
% 23.76/3.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_6]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,X0) ),
% 23.76/3.47      inference(cnf_transformation,[],[f54]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_83,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_3]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1082,plain,
% 23.76/3.47      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 23.76/3.47      theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1091,plain,
% 23.76/3.47      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 23.76/3.47      | k1_xboole_0 != k1_xboole_0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1082]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_4,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 23.76/3.47      inference(cnf_transformation,[],[f55]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1703,plain,
% 23.76/3.47      ( ~ r1_tarski(k2_relset_1(sK7,sK6,sK8),k1_xboole_0)
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_4]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_23,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 23.76/3.47      inference(cnf_transformation,[],[f74]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1760,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_23]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1797,plain,
% 23.76/3.47      ( ~ m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | r1_tarski(k2_relset_1(sK7,sK6,sK8),k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_10]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1840,plain,
% 23.76/3.47      ( X0 != X1
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != X1
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = X0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1077]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2022,plain,
% 23.76/3.47      ( X0 != k2_relat_1(sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = X0
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1840]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2329,plain,
% 23.76/3.47      ( k2_relset_1(X0,X1,sK8) != k2_relat_1(sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(X0,X1,sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_2022]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2331,plain,
% 23.76/3.47      ( k2_relset_1(sK7,sK6,sK8) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relat_1(sK8)
% 23.76/3.47      | k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) != k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_2329]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2330,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.76/3.47      | k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_23]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2333,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 23.76/3.47      | k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k2_relat_1(sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_2330]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1081,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.76/3.47      theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1763,plain,
% 23.76/3.47      ( m1_subset_1(X0,X1)
% 23.76/3.47      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 23.76/3.47      | X0 != X2
% 23.76/3.47      | X1 != k1_zfmisc_1(X3) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1081]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1913,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.76/3.47      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 23.76/3.47      | X2 != X0
% 23.76/3.47      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1763]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2875,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.76/3.47      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 23.76/3.47      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
% 23.76/3.47      | sK8 != X0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1913]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2877,plain,
% 23.76/3.47      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 23.76/3.47      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 23.76/3.47      | sK8 != k1_xboole_0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_2875]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3344,plain,
% 23.76/3.47      ( k2_zfmisc_1(X0,X1) != X2
% 23.76/3.47      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1082]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3345,plain,
% 23.76/3.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.76/3.47      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_3344]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5568,plain,
% 23.76/3.47      ( v1_relat_1(sK8) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_5567]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1906,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.76/3.47      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.76/3.47      | X2 != X0
% 23.76/3.47      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1763]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2182,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != X0
% 23.76/3.47      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1906]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_10030,plain,
% 23.76/3.47      ( ~ m1_subset_1(k2_relset_1(X0,X1,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X0,X1,sK8)
% 23.76/3.47      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_2182]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_10043,plain,
% 23.76/3.47      ( m1_subset_1(k2_relset_1(sK7,sK6,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | ~ m1_subset_1(k2_relset_1(k1_xboole_0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
% 23.76/3.47      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_10030]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_21,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 23.76/3.47      inference(cnf_transformation,[],[f72]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_38597,plain,
% 23.76/3.47      ( m1_subset_1(k2_relset_1(X0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_21]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_38601,plain,
% 23.76/3.47      ( m1_subset_1(k2_relset_1(k1_xboole_0,k1_xboole_0,sK8),k1_zfmisc_1(k1_xboole_0))
% 23.76/3.47      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_38597]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_49909,plain,
% 23.76/3.47      ( m1_subset_1(sK4(sK8),sK7) != iProver_top ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_5177,c_26,c_25,c_72,c_77,c_78,c_83,c_1091,c_1703,
% 23.76/3.47                 c_1760,c_1797,c_2331,c_2333,c_2877,c_3345,c_5568,
% 23.76/3.47                 c_10043,c_38601]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_49911,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK4(sK8),sK7) ),
% 23.76/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_49909]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101596,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK4(sK8),sK7) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_101487,c_26,c_25,c_72,c_77,c_78,c_83,c_1091,c_1703,
% 23.76/3.47                 c_1760,c_1797,c_2331,c_2333,c_2877,c_3345,c_5180,c_5567,
% 23.76/3.47                 c_10043,c_38601]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_8,plain,
% 23.76/3.47      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 23.76/3.47      inference(cnf_transformation,[],[f59]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_101608,plain,
% 23.76/3.47      ( ~ r2_hidden(sK4(sK8),sK7) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_101596,c_8]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3726,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1078,c_1076]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5,plain,
% 23.76/3.47      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.76/3.47      inference(cnf_transformation,[],[f78]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_7502,plain,
% 23.76/3.47      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1)
% 23.76/3.47      | ~ r1_tarski(k1_xboole_0,X1) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_3726,c_5]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_27171,plain,
% 23.76/3.47      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),X1) ),
% 23.76/3.47      inference(forward_subsumption_resolution,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_7502,c_3]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_6493,plain,
% 23.76/3.47      ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_2805,c_5]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3718,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | r1_tarski(X3,k1_relset_1(X1,X2,X0))
% 23.76/3.47      | ~ r1_tarski(X4,k1_relat_1(X0))
% 23.76/3.47      | X3 != X4 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1078,c_22]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2775,plain,
% 23.76/3.47      ( r2_hidden(sK4(X0),k1_relat_1(X0))
% 23.76/3.47      | ~ v1_relat_1(X0)
% 23.76/3.47      | k1_xboole_0 = X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9219,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7) | ~ v1_relat_1(sK8) | k1_xboole_0 = sK8 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_9016,c_2775]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9249,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7) | k1_xboole_0 = sK8 ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_9219,c_5567]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3786,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1081,c_1076]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9461,plain,
% 23.76/3.47      ( ~ m1_subset_1(sK8,X0)
% 23.76/3.47      | m1_subset_1(k1_xboole_0,X0)
% 23.76/3.47      | r2_hidden(sK4(sK8),sK7) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_9249,c_3786]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_10646,plain,
% 23.76/3.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
% 23.76/3.47      | r2_hidden(sK4(sK8),sK7) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_9461,c_26]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_15119,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7)
% 23.76/3.47      | r1_tarski(X0,k1_relset_1(sK7,sK6,k1_xboole_0))
% 23.76/3.47      | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
% 23.76/3.47      | X0 != X1 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_3718,c_10646]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_23843,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7)
% 23.76/3.47      | ~ r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 23.76/3.47      | r1_tarski(k1_xboole_0,k1_relset_1(sK7,sK6,k1_xboole_0)) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_6493,c_15119]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_27377,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7)
% 23.76/3.47      | r1_tarski(k1_xboole_0,k1_relset_1(sK7,sK6,k1_xboole_0)) ),
% 23.76/3.47      inference(backward_subsumption_resolution,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_27171,c_23843]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1747,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_9]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1749,plain,
% 23.76/3.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 23.76/3.47      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1747]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1745,plain,
% 23.76/3.47      ( k2_relset_1(sK7,sK6,sK8) != X0
% 23.76/3.47      | k1_xboole_0 != X0
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1077]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1841,plain,
% 23.76/3.47      ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X0,X1,X2)
% 23.76/3.47      | k1_xboole_0 != k2_relset_1(X0,X1,X2)
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1745]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1843,plain,
% 23.76/3.47      ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(sK7,sK6,sK8)
% 23.76/3.47      | k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1841]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1860,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_3]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1864,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1860]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1641,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1638,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.76/3.47      | r1_tarski(X0,X1) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1628,plain,
% 23.76/3.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 23.76/3.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2202,plain,
% 23.76/3.47      ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
% 23.76/3.47      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_5,c_1628]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2454,plain,
% 23.76/3.47      ( k2_relset_1(X0,k1_xboole_0,X1) = k2_relat_1(X1)
% 23.76/3.47      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_1638,c_2202]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_3961,plain,
% 23.76/3.47      ( k2_relset_1(X0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_1641,c_2454]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1630,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.76/3.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_4043,plain,
% 23.76/3.47      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.76/3.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_3961,c_1630]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1748,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 23.76/3.47      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_1747]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1750,plain,
% 23.76/3.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 23.76/3.47      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1748]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1863,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1865,plain,
% 23.76/3.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1863]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_4045,plain,
% 23.76/3.47      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.76/3.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_4043]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5548,plain,
% 23.76/3.47      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_4043,c_1750,c_1865,c_4045]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1637,plain,
% 23.76/3.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.76/3.47      | r1_tarski(X0,X1) = iProver_top ),
% 23.76/3.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5552,plain,
% 23.76/3.47      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 23.76/3.47      inference(superposition,[status(thm)],[c_5548,c_1637]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_5559,plain,
% 23.76/3.47      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
% 23.76/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_5552]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_2801,plain,
% 23.76/3.47      ( ~ r1_tarski(X0,k1_xboole_0) | X1 != X0 | k1_xboole_0 = X1 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_1077,c_4]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_7828,plain,
% 23.76/3.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.76/3.47      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(X1,X2,X0) ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_2801,c_23]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_7830,plain,
% 23.76/3.47      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 23.76/3.47      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 23.76/3.47      | k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_7828]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_9455,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7) | sK8 = k1_xboole_0 ),
% 23.76/3.47      inference(resolution,[status(thm)],[c_9249,c_2805]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_10071,plain,
% 23.76/3.47      ( X0 != k2_relset_1(X1,X2,sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = X0
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X1,X2,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1840]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_34128,plain,
% 23.76/3.47      ( k2_relset_1(X0,X1,X2) != k2_relset_1(X3,X4,sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(X0,X1,X2)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) != k2_relset_1(X3,X4,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_10071]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_34130,plain,
% 23.76/3.47      ( k2_relset_1(sK7,sK6,sK8) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
% 23.76/3.47      | k2_relset_1(sK7,sK6,sK8) = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 23.76/3.47      | k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k2_relset_1(k1_xboole_0,k1_xboole_0,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_34128]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_1085,plain,
% 23.76/3.47      ( X0 != X1
% 23.76/3.47      | X2 != X3
% 23.76/3.47      | X4 != X5
% 23.76/3.47      | k2_relset_1(X0,X2,X4) = k2_relset_1(X1,X3,X5) ),
% 23.76/3.47      theory(equality) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_34129,plain,
% 23.76/3.47      ( X0 != X1
% 23.76/3.47      | X2 != X3
% 23.76/3.47      | X4 != sK8
% 23.76/3.47      | k2_relset_1(X0,X2,X4) = k2_relset_1(X1,X3,sK8) ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_1085]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_34131,plain,
% 23.76/3.47      ( k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK8)
% 23.76/3.47      | k1_xboole_0 != sK8
% 23.76/3.47      | k1_xboole_0 != k1_xboole_0 ),
% 23.76/3.47      inference(instantiation,[status(thm)],[c_34129]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(c_34258,plain,
% 23.76/3.47      ( r2_hidden(sK4(sK8),sK7) ),
% 23.76/3.47      inference(global_propositional_subsumption,
% 23.76/3.47                [status(thm)],
% 23.76/3.47                [c_27377,c_26,c_25,c_72,c_77,c_78,c_83,c_1749,c_1760,
% 23.76/3.47                 c_1843,c_1864,c_2331,c_2333,c_2877,c_3345,c_5559,c_7830,
% 23.76/3.47                 c_9249,c_9455,c_34130,c_34131]) ).
% 23.76/3.47  
% 23.76/3.47  cnf(contradiction,plain,
% 23.76/3.47      ( $false ),
% 23.76/3.47      inference(minisat,[status(thm)],[c_101608,c_34258]) ).
% 23.76/3.47  
% 23.76/3.47  
% 23.76/3.47  % SZS output end CNFRefutation for theBenchmark.p
% 23.76/3.47  
% 23.76/3.47  ------                               Statistics
% 23.76/3.47  
% 23.76/3.47  ------ Selected
% 23.76/3.47  
% 23.76/3.47  total_time:                             2.889
% 23.76/3.47  
%------------------------------------------------------------------------------
