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
% DateTime   : Thu Dec  3 11:39:35 EST 2020

% Result     : Theorem 23.23s
% Output     : CNFRefutation 23.23s
% Verified   : 
% Statistics : Number of formulae       :  141 (1031 expanded)
%              Number of clauses        :   75 ( 364 expanded)
%              Number of leaves         :   19 ( 221 expanded)
%              Depth                    :   23
%              Number of atoms          :  350 (3659 expanded)
%              Number of equality atoms :  110 ( 621 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f59])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f59])).

fof(f88,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f67,f59])).

fof(f87,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_497,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_498,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_2005,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_498])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1884,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5960,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1884])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1896,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6164,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(k3_subset_1(sK1,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5960,c_1896])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_461,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_462,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_464,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_39])).

cnf(c_1872,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1879,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5416,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1879])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1890,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6007,plain,
    ( k3_xboole_0(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_5416,c_1890])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6309,plain,
    ( k3_xboole_0(sK1,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_6007,c_0])).

cnf(c_6616,plain,
    ( k3_subset_1(sK1,sK3) = k5_xboole_0(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_6309,c_2005])).

cnf(c_9365,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(k5_xboole_0(sK1,sK3),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6164,c_6616])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_479,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_480,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_39])).

cnf(c_1871,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_5417,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1879])).

cnf(c_6162,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_5417,c_1890])).

cnf(c_6383,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_6162,c_0])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1883,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8791,plain,
    ( r1_tarski(X0,k5_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_1883])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1874,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7020,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6616,c_1874])).

cnf(c_506,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_507,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_2006,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_507])).

cnf(c_6627,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6383,c_2006])).

cnf(c_7021,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7020,c_6627])).

cnf(c_91215,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),sK1) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8791,c_7021])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1889,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3405,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1889])).

cnf(c_6307,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6007,c_3405])).

cnf(c_12,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1886,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3101,plain,
    ( r1_xboole_0(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_1886])).

cnf(c_4514,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_1896])).

cnf(c_7037,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6627,c_4514])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1873,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7019,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6616,c_1873])).

cnf(c_7022,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7019,c_6627])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1888,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7779,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),X0) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6309,c_1888])).

cnf(c_61920,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,k5_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7022,c_7779])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1891,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8093,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5417,c_1891])).

cnf(c_62845,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,k5_xboole_0(sK1,sK2))) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_61920,c_8093])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1887,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_63476,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62845,c_1887])).

cnf(c_91786,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91215,c_6307,c_7037,c_63476])).

cnf(c_91790,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9365,c_91786])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91790,c_63476,c_7037])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.23/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.23/3.48  
% 23.23/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.23/3.48  
% 23.23/3.48  ------  iProver source info
% 23.23/3.48  
% 23.23/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.23/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.23/3.48  git: non_committed_changes: false
% 23.23/3.48  git: last_make_outside_of_git: false
% 23.23/3.48  
% 23.23/3.48  ------ 
% 23.23/3.48  
% 23.23/3.48  ------ Input Options
% 23.23/3.48  
% 23.23/3.48  --out_options                           all
% 23.23/3.48  --tptp_safe_out                         true
% 23.23/3.48  --problem_path                          ""
% 23.23/3.48  --include_path                          ""
% 23.23/3.48  --clausifier                            res/vclausify_rel
% 23.23/3.48  --clausifier_options                    ""
% 23.23/3.48  --stdin                                 false
% 23.23/3.48  --stats_out                             all
% 23.23/3.48  
% 23.23/3.48  ------ General Options
% 23.23/3.48  
% 23.23/3.48  --fof                                   false
% 23.23/3.48  --time_out_real                         305.
% 23.23/3.48  --time_out_virtual                      -1.
% 23.23/3.48  --symbol_type_check                     false
% 23.23/3.48  --clausify_out                          false
% 23.23/3.48  --sig_cnt_out                           false
% 23.23/3.48  --trig_cnt_out                          false
% 23.23/3.48  --trig_cnt_out_tolerance                1.
% 23.23/3.48  --trig_cnt_out_sk_spl                   false
% 23.23/3.48  --abstr_cl_out                          false
% 23.23/3.48  
% 23.23/3.48  ------ Global Options
% 23.23/3.48  
% 23.23/3.48  --schedule                              default
% 23.23/3.48  --add_important_lit                     false
% 23.23/3.48  --prop_solver_per_cl                    1000
% 23.23/3.48  --min_unsat_core                        false
% 23.23/3.48  --soft_assumptions                      false
% 23.23/3.48  --soft_lemma_size                       3
% 23.23/3.48  --prop_impl_unit_size                   0
% 23.23/3.48  --prop_impl_unit                        []
% 23.23/3.48  --share_sel_clauses                     true
% 23.23/3.48  --reset_solvers                         false
% 23.23/3.48  --bc_imp_inh                            [conj_cone]
% 23.23/3.48  --conj_cone_tolerance                   3.
% 23.23/3.48  --extra_neg_conj                        none
% 23.23/3.48  --large_theory_mode                     true
% 23.23/3.48  --prolific_symb_bound                   200
% 23.23/3.48  --lt_threshold                          2000
% 23.23/3.48  --clause_weak_htbl                      true
% 23.23/3.48  --gc_record_bc_elim                     false
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing Options
% 23.23/3.48  
% 23.23/3.48  --preprocessing_flag                    true
% 23.23/3.48  --time_out_prep_mult                    0.1
% 23.23/3.48  --splitting_mode                        input
% 23.23/3.48  --splitting_grd                         true
% 23.23/3.48  --splitting_cvd                         false
% 23.23/3.48  --splitting_cvd_svl                     false
% 23.23/3.48  --splitting_nvd                         32
% 23.23/3.48  --sub_typing                            true
% 23.23/3.48  --prep_gs_sim                           true
% 23.23/3.48  --prep_unflatten                        true
% 23.23/3.48  --prep_res_sim                          true
% 23.23/3.48  --prep_upred                            true
% 23.23/3.48  --prep_sem_filter                       exhaustive
% 23.23/3.48  --prep_sem_filter_out                   false
% 23.23/3.48  --pred_elim                             true
% 23.23/3.48  --res_sim_input                         true
% 23.23/3.48  --eq_ax_congr_red                       true
% 23.23/3.48  --pure_diseq_elim                       true
% 23.23/3.48  --brand_transform                       false
% 23.23/3.48  --non_eq_to_eq                          false
% 23.23/3.48  --prep_def_merge                        true
% 23.23/3.48  --prep_def_merge_prop_impl              false
% 23.23/3.48  --prep_def_merge_mbd                    true
% 23.23/3.48  --prep_def_merge_tr_red                 false
% 23.23/3.48  --prep_def_merge_tr_cl                  false
% 23.23/3.48  --smt_preprocessing                     true
% 23.23/3.48  --smt_ac_axioms                         fast
% 23.23/3.48  --preprocessed_out                      false
% 23.23/3.48  --preprocessed_stats                    false
% 23.23/3.48  
% 23.23/3.48  ------ Abstraction refinement Options
% 23.23/3.48  
% 23.23/3.48  --abstr_ref                             []
% 23.23/3.48  --abstr_ref_prep                        false
% 23.23/3.48  --abstr_ref_until_sat                   false
% 23.23/3.48  --abstr_ref_sig_restrict                funpre
% 23.23/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.23/3.48  --abstr_ref_under                       []
% 23.23/3.48  
% 23.23/3.48  ------ SAT Options
% 23.23/3.48  
% 23.23/3.48  --sat_mode                              false
% 23.23/3.48  --sat_fm_restart_options                ""
% 23.23/3.48  --sat_gr_def                            false
% 23.23/3.48  --sat_epr_types                         true
% 23.23/3.48  --sat_non_cyclic_types                  false
% 23.23/3.48  --sat_finite_models                     false
% 23.23/3.48  --sat_fm_lemmas                         false
% 23.23/3.48  --sat_fm_prep                           false
% 23.23/3.48  --sat_fm_uc_incr                        true
% 23.23/3.48  --sat_out_model                         small
% 23.23/3.48  --sat_out_clauses                       false
% 23.23/3.48  
% 23.23/3.48  ------ QBF Options
% 23.23/3.48  
% 23.23/3.48  --qbf_mode                              false
% 23.23/3.48  --qbf_elim_univ                         false
% 23.23/3.48  --qbf_dom_inst                          none
% 23.23/3.48  --qbf_dom_pre_inst                      false
% 23.23/3.48  --qbf_sk_in                             false
% 23.23/3.48  --qbf_pred_elim                         true
% 23.23/3.48  --qbf_split                             512
% 23.23/3.48  
% 23.23/3.48  ------ BMC1 Options
% 23.23/3.48  
% 23.23/3.48  --bmc1_incremental                      false
% 23.23/3.48  --bmc1_axioms                           reachable_all
% 23.23/3.48  --bmc1_min_bound                        0
% 23.23/3.48  --bmc1_max_bound                        -1
% 23.23/3.48  --bmc1_max_bound_default                -1
% 23.23/3.48  --bmc1_symbol_reachability              true
% 23.23/3.48  --bmc1_property_lemmas                  false
% 23.23/3.48  --bmc1_k_induction                      false
% 23.23/3.48  --bmc1_non_equiv_states                 false
% 23.23/3.48  --bmc1_deadlock                         false
% 23.23/3.48  --bmc1_ucm                              false
% 23.23/3.48  --bmc1_add_unsat_core                   none
% 23.23/3.48  --bmc1_unsat_core_children              false
% 23.23/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.23/3.48  --bmc1_out_stat                         full
% 23.23/3.48  --bmc1_ground_init                      false
% 23.23/3.48  --bmc1_pre_inst_next_state              false
% 23.23/3.48  --bmc1_pre_inst_state                   false
% 23.23/3.48  --bmc1_pre_inst_reach_state             false
% 23.23/3.48  --bmc1_out_unsat_core                   false
% 23.23/3.48  --bmc1_aig_witness_out                  false
% 23.23/3.48  --bmc1_verbose                          false
% 23.23/3.48  --bmc1_dump_clauses_tptp                false
% 23.23/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.23/3.48  --bmc1_dump_file                        -
% 23.23/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.23/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.23/3.48  --bmc1_ucm_extend_mode                  1
% 23.23/3.48  --bmc1_ucm_init_mode                    2
% 23.23/3.48  --bmc1_ucm_cone_mode                    none
% 23.23/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.23/3.48  --bmc1_ucm_relax_model                  4
% 23.23/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.23/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.23/3.48  --bmc1_ucm_layered_model                none
% 23.23/3.48  --bmc1_ucm_max_lemma_size               10
% 23.23/3.48  
% 23.23/3.48  ------ AIG Options
% 23.23/3.48  
% 23.23/3.48  --aig_mode                              false
% 23.23/3.48  
% 23.23/3.48  ------ Instantiation Options
% 23.23/3.48  
% 23.23/3.48  --instantiation_flag                    true
% 23.23/3.48  --inst_sos_flag                         true
% 23.23/3.48  --inst_sos_phase                        true
% 23.23/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.23/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.23/3.48  --inst_lit_sel_side                     num_symb
% 23.23/3.48  --inst_solver_per_active                1400
% 23.23/3.48  --inst_solver_calls_frac                1.
% 23.23/3.48  --inst_passive_queue_type               priority_queues
% 23.23/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.23/3.48  --inst_passive_queues_freq              [25;2]
% 23.23/3.48  --inst_dismatching                      true
% 23.23/3.48  --inst_eager_unprocessed_to_passive     true
% 23.23/3.48  --inst_prop_sim_given                   true
% 23.23/3.48  --inst_prop_sim_new                     false
% 23.23/3.48  --inst_subs_new                         false
% 23.23/3.48  --inst_eq_res_simp                      false
% 23.23/3.48  --inst_subs_given                       false
% 23.23/3.48  --inst_orphan_elimination               true
% 23.23/3.48  --inst_learning_loop_flag               true
% 23.23/3.48  --inst_learning_start                   3000
% 23.23/3.48  --inst_learning_factor                  2
% 23.23/3.48  --inst_start_prop_sim_after_learn       3
% 23.23/3.48  --inst_sel_renew                        solver
% 23.23/3.48  --inst_lit_activity_flag                true
% 23.23/3.48  --inst_restr_to_given                   false
% 23.23/3.48  --inst_activity_threshold               500
% 23.23/3.48  --inst_out_proof                        true
% 23.23/3.48  
% 23.23/3.48  ------ Resolution Options
% 23.23/3.48  
% 23.23/3.48  --resolution_flag                       true
% 23.23/3.48  --res_lit_sel                           adaptive
% 23.23/3.48  --res_lit_sel_side                      none
% 23.23/3.48  --res_ordering                          kbo
% 23.23/3.48  --res_to_prop_solver                    active
% 23.23/3.48  --res_prop_simpl_new                    false
% 23.23/3.48  --res_prop_simpl_given                  true
% 23.23/3.48  --res_passive_queue_type                priority_queues
% 23.23/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.23/3.48  --res_passive_queues_freq               [15;5]
% 23.23/3.48  --res_forward_subs                      full
% 23.23/3.48  --res_backward_subs                     full
% 23.23/3.48  --res_forward_subs_resolution           true
% 23.23/3.48  --res_backward_subs_resolution          true
% 23.23/3.48  --res_orphan_elimination                true
% 23.23/3.48  --res_time_limit                        2.
% 23.23/3.48  --res_out_proof                         true
% 23.23/3.48  
% 23.23/3.48  ------ Superposition Options
% 23.23/3.48  
% 23.23/3.48  --superposition_flag                    true
% 23.23/3.48  --sup_passive_queue_type                priority_queues
% 23.23/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.23/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.23/3.48  --demod_completeness_check              fast
% 23.23/3.48  --demod_use_ground                      true
% 23.23/3.48  --sup_to_prop_solver                    passive
% 23.23/3.48  --sup_prop_simpl_new                    true
% 23.23/3.48  --sup_prop_simpl_given                  true
% 23.23/3.48  --sup_fun_splitting                     true
% 23.23/3.48  --sup_smt_interval                      50000
% 23.23/3.48  
% 23.23/3.48  ------ Superposition Simplification Setup
% 23.23/3.48  
% 23.23/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.23/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.23/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.23/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.23/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.23/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.23/3.48  --sup_immed_triv                        [TrivRules]
% 23.23/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_immed_bw_main                     []
% 23.23/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.23/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.23/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_input_bw                          []
% 23.23/3.48  
% 23.23/3.48  ------ Combination Options
% 23.23/3.48  
% 23.23/3.48  --comb_res_mult                         3
% 23.23/3.48  --comb_sup_mult                         2
% 23.23/3.48  --comb_inst_mult                        10
% 23.23/3.48  
% 23.23/3.48  ------ Debug Options
% 23.23/3.48  
% 23.23/3.48  --dbg_backtrace                         false
% 23.23/3.48  --dbg_dump_prop_clauses                 false
% 23.23/3.48  --dbg_dump_prop_clauses_file            -
% 23.23/3.48  --dbg_out_stat                          false
% 23.23/3.48  ------ Parsing...
% 23.23/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.23/3.48  ------ Proving...
% 23.23/3.48  ------ Problem Properties 
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  clauses                                 30
% 23.23/3.48  conjectures                             2
% 23.23/3.48  EPR                                     4
% 23.23/3.48  Horn                                    28
% 23.23/3.48  unary                                   8
% 23.23/3.48  binary                                  16
% 23.23/3.48  lits                                    58
% 23.23/3.48  lits eq                                 11
% 23.23/3.48  fd_pure                                 0
% 23.23/3.48  fd_pseudo                               0
% 23.23/3.48  fd_cond                                 0
% 23.23/3.48  fd_pseudo_cond                          3
% 23.23/3.48  AC symbols                              0
% 23.23/3.48  
% 23.23/3.48  ------ Schedule dynamic 5 is on 
% 23.23/3.48  
% 23.23/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  ------ 
% 23.23/3.48  Current options:
% 23.23/3.48  ------ 
% 23.23/3.48  
% 23.23/3.48  ------ Input Options
% 23.23/3.48  
% 23.23/3.48  --out_options                           all
% 23.23/3.48  --tptp_safe_out                         true
% 23.23/3.48  --problem_path                          ""
% 23.23/3.48  --include_path                          ""
% 23.23/3.48  --clausifier                            res/vclausify_rel
% 23.23/3.48  --clausifier_options                    ""
% 23.23/3.48  --stdin                                 false
% 23.23/3.48  --stats_out                             all
% 23.23/3.48  
% 23.23/3.48  ------ General Options
% 23.23/3.48  
% 23.23/3.48  --fof                                   false
% 23.23/3.48  --time_out_real                         305.
% 23.23/3.48  --time_out_virtual                      -1.
% 23.23/3.48  --symbol_type_check                     false
% 23.23/3.48  --clausify_out                          false
% 23.23/3.48  --sig_cnt_out                           false
% 23.23/3.48  --trig_cnt_out                          false
% 23.23/3.48  --trig_cnt_out_tolerance                1.
% 23.23/3.48  --trig_cnt_out_sk_spl                   false
% 23.23/3.48  --abstr_cl_out                          false
% 23.23/3.48  
% 23.23/3.48  ------ Global Options
% 23.23/3.48  
% 23.23/3.48  --schedule                              default
% 23.23/3.48  --add_important_lit                     false
% 23.23/3.48  --prop_solver_per_cl                    1000
% 23.23/3.48  --min_unsat_core                        false
% 23.23/3.48  --soft_assumptions                      false
% 23.23/3.48  --soft_lemma_size                       3
% 23.23/3.48  --prop_impl_unit_size                   0
% 23.23/3.48  --prop_impl_unit                        []
% 23.23/3.48  --share_sel_clauses                     true
% 23.23/3.48  --reset_solvers                         false
% 23.23/3.48  --bc_imp_inh                            [conj_cone]
% 23.23/3.48  --conj_cone_tolerance                   3.
% 23.23/3.48  --extra_neg_conj                        none
% 23.23/3.48  --large_theory_mode                     true
% 23.23/3.48  --prolific_symb_bound                   200
% 23.23/3.48  --lt_threshold                          2000
% 23.23/3.48  --clause_weak_htbl                      true
% 23.23/3.48  --gc_record_bc_elim                     false
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing Options
% 23.23/3.48  
% 23.23/3.48  --preprocessing_flag                    true
% 23.23/3.48  --time_out_prep_mult                    0.1
% 23.23/3.48  --splitting_mode                        input
% 23.23/3.48  --splitting_grd                         true
% 23.23/3.48  --splitting_cvd                         false
% 23.23/3.48  --splitting_cvd_svl                     false
% 23.23/3.48  --splitting_nvd                         32
% 23.23/3.48  --sub_typing                            true
% 23.23/3.48  --prep_gs_sim                           true
% 23.23/3.48  --prep_unflatten                        true
% 23.23/3.48  --prep_res_sim                          true
% 23.23/3.48  --prep_upred                            true
% 23.23/3.48  --prep_sem_filter                       exhaustive
% 23.23/3.48  --prep_sem_filter_out                   false
% 23.23/3.48  --pred_elim                             true
% 23.23/3.48  --res_sim_input                         true
% 23.23/3.48  --eq_ax_congr_red                       true
% 23.23/3.48  --pure_diseq_elim                       true
% 23.23/3.48  --brand_transform                       false
% 23.23/3.48  --non_eq_to_eq                          false
% 23.23/3.48  --prep_def_merge                        true
% 23.23/3.48  --prep_def_merge_prop_impl              false
% 23.23/3.48  --prep_def_merge_mbd                    true
% 23.23/3.48  --prep_def_merge_tr_red                 false
% 23.23/3.48  --prep_def_merge_tr_cl                  false
% 23.23/3.48  --smt_preprocessing                     true
% 23.23/3.48  --smt_ac_axioms                         fast
% 23.23/3.48  --preprocessed_out                      false
% 23.23/3.48  --preprocessed_stats                    false
% 23.23/3.48  
% 23.23/3.48  ------ Abstraction refinement Options
% 23.23/3.48  
% 23.23/3.48  --abstr_ref                             []
% 23.23/3.48  --abstr_ref_prep                        false
% 23.23/3.48  --abstr_ref_until_sat                   false
% 23.23/3.48  --abstr_ref_sig_restrict                funpre
% 23.23/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.23/3.48  --abstr_ref_under                       []
% 23.23/3.48  
% 23.23/3.48  ------ SAT Options
% 23.23/3.48  
% 23.23/3.48  --sat_mode                              false
% 23.23/3.48  --sat_fm_restart_options                ""
% 23.23/3.48  --sat_gr_def                            false
% 23.23/3.48  --sat_epr_types                         true
% 23.23/3.48  --sat_non_cyclic_types                  false
% 23.23/3.48  --sat_finite_models                     false
% 23.23/3.48  --sat_fm_lemmas                         false
% 23.23/3.48  --sat_fm_prep                           false
% 23.23/3.48  --sat_fm_uc_incr                        true
% 23.23/3.48  --sat_out_model                         small
% 23.23/3.48  --sat_out_clauses                       false
% 23.23/3.48  
% 23.23/3.48  ------ QBF Options
% 23.23/3.48  
% 23.23/3.48  --qbf_mode                              false
% 23.23/3.48  --qbf_elim_univ                         false
% 23.23/3.48  --qbf_dom_inst                          none
% 23.23/3.48  --qbf_dom_pre_inst                      false
% 23.23/3.48  --qbf_sk_in                             false
% 23.23/3.48  --qbf_pred_elim                         true
% 23.23/3.48  --qbf_split                             512
% 23.23/3.48  
% 23.23/3.48  ------ BMC1 Options
% 23.23/3.48  
% 23.23/3.48  --bmc1_incremental                      false
% 23.23/3.48  --bmc1_axioms                           reachable_all
% 23.23/3.48  --bmc1_min_bound                        0
% 23.23/3.48  --bmc1_max_bound                        -1
% 23.23/3.48  --bmc1_max_bound_default                -1
% 23.23/3.48  --bmc1_symbol_reachability              true
% 23.23/3.48  --bmc1_property_lemmas                  false
% 23.23/3.48  --bmc1_k_induction                      false
% 23.23/3.48  --bmc1_non_equiv_states                 false
% 23.23/3.48  --bmc1_deadlock                         false
% 23.23/3.48  --bmc1_ucm                              false
% 23.23/3.48  --bmc1_add_unsat_core                   none
% 23.23/3.48  --bmc1_unsat_core_children              false
% 23.23/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.23/3.48  --bmc1_out_stat                         full
% 23.23/3.48  --bmc1_ground_init                      false
% 23.23/3.48  --bmc1_pre_inst_next_state              false
% 23.23/3.48  --bmc1_pre_inst_state                   false
% 23.23/3.48  --bmc1_pre_inst_reach_state             false
% 23.23/3.48  --bmc1_out_unsat_core                   false
% 23.23/3.48  --bmc1_aig_witness_out                  false
% 23.23/3.48  --bmc1_verbose                          false
% 23.23/3.48  --bmc1_dump_clauses_tptp                false
% 23.23/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.23/3.48  --bmc1_dump_file                        -
% 23.23/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.23/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.23/3.48  --bmc1_ucm_extend_mode                  1
% 23.23/3.48  --bmc1_ucm_init_mode                    2
% 23.23/3.48  --bmc1_ucm_cone_mode                    none
% 23.23/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.23/3.48  --bmc1_ucm_relax_model                  4
% 23.23/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.23/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.23/3.48  --bmc1_ucm_layered_model                none
% 23.23/3.48  --bmc1_ucm_max_lemma_size               10
% 23.23/3.48  
% 23.23/3.48  ------ AIG Options
% 23.23/3.48  
% 23.23/3.48  --aig_mode                              false
% 23.23/3.48  
% 23.23/3.48  ------ Instantiation Options
% 23.23/3.48  
% 23.23/3.48  --instantiation_flag                    true
% 23.23/3.48  --inst_sos_flag                         true
% 23.23/3.48  --inst_sos_phase                        true
% 23.23/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.23/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.23/3.48  --inst_lit_sel_side                     none
% 23.23/3.48  --inst_solver_per_active                1400
% 23.23/3.48  --inst_solver_calls_frac                1.
% 23.23/3.48  --inst_passive_queue_type               priority_queues
% 23.23/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.23/3.48  --inst_passive_queues_freq              [25;2]
% 23.23/3.48  --inst_dismatching                      true
% 23.23/3.48  --inst_eager_unprocessed_to_passive     true
% 23.23/3.48  --inst_prop_sim_given                   true
% 23.23/3.48  --inst_prop_sim_new                     false
% 23.23/3.48  --inst_subs_new                         false
% 23.23/3.48  --inst_eq_res_simp                      false
% 23.23/3.48  --inst_subs_given                       false
% 23.23/3.48  --inst_orphan_elimination               true
% 23.23/3.48  --inst_learning_loop_flag               true
% 23.23/3.48  --inst_learning_start                   3000
% 23.23/3.48  --inst_learning_factor                  2
% 23.23/3.48  --inst_start_prop_sim_after_learn       3
% 23.23/3.48  --inst_sel_renew                        solver
% 23.23/3.48  --inst_lit_activity_flag                true
% 23.23/3.48  --inst_restr_to_given                   false
% 23.23/3.48  --inst_activity_threshold               500
% 23.23/3.48  --inst_out_proof                        true
% 23.23/3.48  
% 23.23/3.48  ------ Resolution Options
% 23.23/3.48  
% 23.23/3.48  --resolution_flag                       false
% 23.23/3.48  --res_lit_sel                           adaptive
% 23.23/3.48  --res_lit_sel_side                      none
% 23.23/3.48  --res_ordering                          kbo
% 23.23/3.48  --res_to_prop_solver                    active
% 23.23/3.48  --res_prop_simpl_new                    false
% 23.23/3.48  --res_prop_simpl_given                  true
% 23.23/3.48  --res_passive_queue_type                priority_queues
% 23.23/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.23/3.48  --res_passive_queues_freq               [15;5]
% 23.23/3.48  --res_forward_subs                      full
% 23.23/3.48  --res_backward_subs                     full
% 23.23/3.48  --res_forward_subs_resolution           true
% 23.23/3.48  --res_backward_subs_resolution          true
% 23.23/3.48  --res_orphan_elimination                true
% 23.23/3.48  --res_time_limit                        2.
% 23.23/3.48  --res_out_proof                         true
% 23.23/3.48  
% 23.23/3.48  ------ Superposition Options
% 23.23/3.48  
% 23.23/3.48  --superposition_flag                    true
% 23.23/3.48  --sup_passive_queue_type                priority_queues
% 23.23/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.23/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.23/3.48  --demod_completeness_check              fast
% 23.23/3.48  --demod_use_ground                      true
% 23.23/3.48  --sup_to_prop_solver                    passive
% 23.23/3.48  --sup_prop_simpl_new                    true
% 23.23/3.48  --sup_prop_simpl_given                  true
% 23.23/3.48  --sup_fun_splitting                     true
% 23.23/3.48  --sup_smt_interval                      50000
% 23.23/3.48  
% 23.23/3.48  ------ Superposition Simplification Setup
% 23.23/3.48  
% 23.23/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.23/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.23/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.23/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.23/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.23/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.23/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.23/3.48  --sup_immed_triv                        [TrivRules]
% 23.23/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_immed_bw_main                     []
% 23.23/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.23/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.23/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.23/3.48  --sup_input_bw                          []
% 23.23/3.48  
% 23.23/3.48  ------ Combination Options
% 23.23/3.48  
% 23.23/3.48  --comb_res_mult                         3
% 23.23/3.48  --comb_sup_mult                         2
% 23.23/3.48  --comb_inst_mult                        10
% 23.23/3.48  
% 23.23/3.48  ------ Debug Options
% 23.23/3.48  
% 23.23/3.48  --dbg_backtrace                         false
% 23.23/3.48  --dbg_dump_prop_clauses                 false
% 23.23/3.48  --dbg_dump_prop_clauses_file            -
% 23.23/3.48  --dbg_out_stat                          false
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  ------ Proving...
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  % SZS status Theorem for theBenchmark.p
% 23.23/3.48  
% 23.23/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.23/3.48  
% 23.23/3.48  fof(f21,axiom,(
% 23.23/3.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f39,plain,(
% 23.23/3.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.23/3.48    inference(ennf_transformation,[],[f21])).
% 23.23/3.48  
% 23.23/3.48  fof(f83,plain,(
% 23.23/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.23/3.48    inference(cnf_transformation,[],[f39])).
% 23.23/3.48  
% 23.23/3.48  fof(f4,axiom,(
% 23.23/3.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f59,plain,(
% 23.23/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.23/3.48    inference(cnf_transformation,[],[f4])).
% 23.23/3.48  
% 23.23/3.48  fof(f94,plain,(
% 23.23/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.23/3.48    inference(definition_unfolding,[],[f83,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f23,conjecture,(
% 23.23/3.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f24,negated_conjecture,(
% 23.23/3.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 23.23/3.48    inference(negated_conjecture,[],[f23])).
% 23.23/3.48  
% 23.23/3.48  fof(f40,plain,(
% 23.23/3.48    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.23/3.48    inference(ennf_transformation,[],[f24])).
% 23.23/3.48  
% 23.23/3.48  fof(f49,plain,(
% 23.23/3.48    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.23/3.48    inference(nnf_transformation,[],[f40])).
% 23.23/3.48  
% 23.23/3.48  fof(f50,plain,(
% 23.23/3.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.23/3.48    inference(flattening,[],[f49])).
% 23.23/3.48  
% 23.23/3.48  fof(f52,plain,(
% 23.23/3.48    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 23.23/3.48    introduced(choice_axiom,[])).
% 23.23/3.48  
% 23.23/3.48  fof(f51,plain,(
% 23.23/3.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 23.23/3.48    introduced(choice_axiom,[])).
% 23.23/3.48  
% 23.23/3.48  fof(f53,plain,(
% 23.23/3.48    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.23/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f52,f51])).
% 23.23/3.48  
% 23.23/3.48  fof(f86,plain,(
% 23.23/3.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 23.23/3.48    inference(cnf_transformation,[],[f53])).
% 23.23/3.48  
% 23.23/3.48  fof(f14,axiom,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f33,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 23.23/3.48    inference(ennf_transformation,[],[f14])).
% 23.23/3.48  
% 23.23/3.48  fof(f69,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f33])).
% 23.23/3.48  
% 23.23/3.48  fof(f92,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(definition_unfolding,[],[f69,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f2,axiom,(
% 23.23/3.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f25,plain,(
% 23.23/3.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 23.23/3.48    inference(ennf_transformation,[],[f2])).
% 23.23/3.48  
% 23.23/3.48  fof(f55,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f25])).
% 23.23/3.48  
% 23.23/3.48  fof(f20,axiom,(
% 23.23/3.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f38,plain,(
% 23.23/3.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.23/3.48    inference(ennf_transformation,[],[f20])).
% 23.23/3.48  
% 23.23/3.48  fof(f48,plain,(
% 23.23/3.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.23/3.48    inference(nnf_transformation,[],[f38])).
% 23.23/3.48  
% 23.23/3.48  fof(f79,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f48])).
% 23.23/3.48  
% 23.23/3.48  fof(f22,axiom,(
% 23.23/3.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f84,plain,(
% 23.23/3.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.23/3.48    inference(cnf_transformation,[],[f22])).
% 23.23/3.48  
% 23.23/3.48  fof(f16,axiom,(
% 23.23/3.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f43,plain,(
% 23.23/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.23/3.48    inference(nnf_transformation,[],[f16])).
% 23.23/3.48  
% 23.23/3.48  fof(f44,plain,(
% 23.23/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.23/3.48    inference(rectify,[],[f43])).
% 23.23/3.48  
% 23.23/3.48  fof(f45,plain,(
% 23.23/3.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 23.23/3.48    introduced(choice_axiom,[])).
% 23.23/3.48  
% 23.23/3.48  fof(f46,plain,(
% 23.23/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.23/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 23.23/3.48  
% 23.23/3.48  fof(f71,plain,(
% 23.23/3.48    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.23/3.48    inference(cnf_transformation,[],[f46])).
% 23.23/3.48  
% 23.23/3.48  fof(f98,plain,(
% 23.23/3.48    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.23/3.48    inference(equality_resolution,[],[f71])).
% 23.23/3.48  
% 23.23/3.48  fof(f8,axiom,(
% 23.23/3.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f29,plain,(
% 23.23/3.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.23/3.48    inference(ennf_transformation,[],[f8])).
% 23.23/3.48  
% 23.23/3.48  fof(f63,plain,(
% 23.23/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f29])).
% 23.23/3.48  
% 23.23/3.48  fof(f1,axiom,(
% 23.23/3.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f54,plain,(
% 23.23/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f1])).
% 23.23/3.48  
% 23.23/3.48  fof(f85,plain,(
% 23.23/3.48    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.23/3.48    inference(cnf_transformation,[],[f53])).
% 23.23/3.48  
% 23.23/3.48  fof(f15,axiom,(
% 23.23/3.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f34,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.23/3.48    inference(ennf_transformation,[],[f15])).
% 23.23/3.48  
% 23.23/3.48  fof(f35,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 23.23/3.48    inference(flattening,[],[f34])).
% 23.23/3.48  
% 23.23/3.48  fof(f70,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f35])).
% 23.23/3.48  
% 23.23/3.48  fof(f93,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(definition_unfolding,[],[f70,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f88,plain,(
% 23.23/3.48    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 23.23/3.48    inference(cnf_transformation,[],[f53])).
% 23.23/3.48  
% 23.23/3.48  fof(f9,axiom,(
% 23.23/3.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f64,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f9])).
% 23.23/3.48  
% 23.23/3.48  fof(f89,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 23.23/3.48    inference(definition_unfolding,[],[f64,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f12,axiom,(
% 23.23/3.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f67,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f12])).
% 23.23/3.48  
% 23.23/3.48  fof(f91,plain,(
% 23.23/3.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 23.23/3.48    inference(definition_unfolding,[],[f67,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f87,plain,(
% 23.23/3.48    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 23.23/3.48    inference(cnf_transformation,[],[f53])).
% 23.23/3.48  
% 23.23/3.48  fof(f10,axiom,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f30,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.23/3.48    inference(ennf_transformation,[],[f10])).
% 23.23/3.48  
% 23.23/3.48  fof(f65,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f30])).
% 23.23/3.48  
% 23.23/3.48  fof(f90,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 23.23/3.48    inference(definition_unfolding,[],[f65,f59])).
% 23.23/3.48  
% 23.23/3.48  fof(f7,axiom,(
% 23.23/3.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f27,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.23/3.48    inference(ennf_transformation,[],[f7])).
% 23.23/3.48  
% 23.23/3.48  fof(f28,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 23.23/3.48    inference(flattening,[],[f27])).
% 23.23/3.48  
% 23.23/3.48  fof(f62,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.23/3.48    inference(cnf_transformation,[],[f28])).
% 23.23/3.48  
% 23.23/3.48  fof(f11,axiom,(
% 23.23/3.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 23.23/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.23/3.48  
% 23.23/3.48  fof(f31,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 23.23/3.48    inference(ennf_transformation,[],[f11])).
% 23.23/3.48  
% 23.23/3.48  fof(f32,plain,(
% 23.23/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.23/3.48    inference(flattening,[],[f31])).
% 23.23/3.48  
% 23.23/3.48  fof(f66,plain,(
% 23.23/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.23/3.48    inference(cnf_transformation,[],[f32])).
% 23.23/3.48  
% 23.23/3.48  cnf(c_28,plain,
% 23.23/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.23/3.48      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 23.23/3.48      inference(cnf_transformation,[],[f94]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_32,negated_conjecture,
% 23.23/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(cnf_transformation,[],[f86]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_497,plain,
% 23.23/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 23.23/3.48      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 23.23/3.48      | sK3 != X1 ),
% 23.23/3.48      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_498,plain,
% 23.23/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 23.23/3.48      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 23.23/3.48      inference(unflattening,[status(thm)],[c_497]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_2005,plain,
% 23.23/3.48      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 23.23/3.48      inference(equality_resolution,[status(thm)],[c_498]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_14,plain,
% 23.23/3.48      ( ~ r1_tarski(X0,X1)
% 23.23/3.48      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 23.23/3.48      inference(cnf_transformation,[],[f92]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1884,plain,
% 23.23/3.48      ( r1_tarski(X0,X1) != iProver_top
% 23.23/3.48      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_5960,plain,
% 23.23/3.48      ( r1_tarski(X0,sK3) != iProver_top
% 23.23/3.48      | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_2005,c_1884]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1,plain,
% 23.23/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.23/3.48      inference(cnf_transformation,[],[f55]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1896,plain,
% 23.23/3.48      ( r1_xboole_0(X0,X1) != iProver_top
% 23.23/3.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6164,plain,
% 23.23/3.48      ( r1_tarski(X0,sK3) != iProver_top
% 23.23/3.48      | r1_xboole_0(k3_subset_1(sK1,sK3),X0) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_5960,c_1896]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_27,plain,
% 23.23/3.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.23/3.48      inference(cnf_transformation,[],[f79]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_461,plain,
% 23.23/3.48      ( r2_hidden(X0,X1)
% 23.23/3.48      | v1_xboole_0(X1)
% 23.23/3.48      | k1_zfmisc_1(sK1) != X1
% 23.23/3.48      | sK3 != X0 ),
% 23.23/3.48      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_462,plain,
% 23.23/3.48      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(unflattening,[status(thm)],[c_461]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_29,plain,
% 23.23/3.48      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.23/3.48      inference(cnf_transformation,[],[f84]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_39,plain,
% 23.23/3.48      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(instantiation,[status(thm)],[c_29]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_464,plain,
% 23.23/3.48      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(global_propositional_subsumption,
% 23.23/3.48                [status(thm)],
% 23.23/3.48                [c_462,c_39]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1872,plain,
% 23.23/3.48      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_19,plain,
% 23.23/3.48      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.23/3.48      inference(cnf_transformation,[],[f98]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1879,plain,
% 23.23/3.48      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.23/3.48      | r1_tarski(X0,X1) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_5416,plain,
% 23.23/3.48      ( r1_tarski(sK3,sK1) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_1872,c_1879]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_8,plain,
% 23.23/3.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.23/3.48      inference(cnf_transformation,[],[f63]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1890,plain,
% 23.23/3.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6007,plain,
% 23.23/3.48      ( k3_xboole_0(sK3,sK1) = sK3 ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_5416,c_1890]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_0,plain,
% 23.23/3.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.23/3.48      inference(cnf_transformation,[],[f54]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6309,plain,
% 23.23/3.48      ( k3_xboole_0(sK1,sK3) = sK3 ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_6007,c_0]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6616,plain,
% 23.23/3.48      ( k3_subset_1(sK1,sK3) = k5_xboole_0(sK1,sK3) ),
% 23.23/3.48      inference(demodulation,[status(thm)],[c_6309,c_2005]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_9365,plain,
% 23.23/3.48      ( r1_tarski(X0,sK3) != iProver_top
% 23.23/3.48      | r1_xboole_0(k5_xboole_0(sK1,sK3),X0) = iProver_top ),
% 23.23/3.48      inference(light_normalisation,[status(thm)],[c_6164,c_6616]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_33,negated_conjecture,
% 23.23/3.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(cnf_transformation,[],[f85]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_479,plain,
% 23.23/3.48      ( r2_hidden(X0,X1)
% 23.23/3.48      | v1_xboole_0(X1)
% 23.23/3.48      | k1_zfmisc_1(sK1) != X1
% 23.23/3.48      | sK2 != X0 ),
% 23.23/3.48      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_480,plain,
% 23.23/3.48      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(unflattening,[status(thm)],[c_479]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_482,plain,
% 23.23/3.48      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 23.23/3.48      inference(global_propositional_subsumption,
% 23.23/3.48                [status(thm)],
% 23.23/3.48                [c_480,c_39]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1871,plain,
% 23.23/3.48      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_5417,plain,
% 23.23/3.48      ( r1_tarski(sK2,sK1) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_1871,c_1879]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6162,plain,
% 23.23/3.48      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_5417,c_1890]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6383,plain,
% 23.23/3.48      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_6162,c_0]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_15,plain,
% 23.23/3.48      ( ~ r1_tarski(X0,X1)
% 23.23/3.48      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 23.23/3.48      | ~ r1_xboole_0(X0,X2) ),
% 23.23/3.48      inference(cnf_transformation,[],[f93]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1883,plain,
% 23.23/3.48      ( r1_tarski(X0,X1) != iProver_top
% 23.23/3.48      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 23.23/3.48      | r1_xboole_0(X0,X2) != iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_8791,plain,
% 23.23/3.48      ( r1_tarski(X0,k5_xboole_0(sK1,sK2)) = iProver_top
% 23.23/3.48      | r1_tarski(X0,sK1) != iProver_top
% 23.23/3.48      | r1_xboole_0(X0,sK2) != iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_6383,c_1883]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_30,negated_conjecture,
% 23.23/3.48      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 23.23/3.48      | ~ r1_tarski(sK2,sK3) ),
% 23.23/3.48      inference(cnf_transformation,[],[f88]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1874,plain,
% 23.23/3.48      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7020,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.23/3.48      inference(demodulation,[status(thm)],[c_6616,c_1874]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_506,plain,
% 23.23/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 23.23/3.48      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 23.23/3.48      | sK2 != X1 ),
% 23.23/3.48      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_507,plain,
% 23.23/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 23.23/3.48      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 23.23/3.48      inference(unflattening,[status(thm)],[c_506]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_2006,plain,
% 23.23/3.48      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 23.23/3.48      inference(equality_resolution,[status(thm)],[c_507]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6627,plain,
% 23.23/3.48      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 23.23/3.48      inference(demodulation,[status(thm)],[c_6383,c_2006]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7021,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) != iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.23/3.48      inference(light_normalisation,[status(thm)],[c_7020,c_6627]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_91215,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),sK1) != iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) != iProver_top
% 23.23/3.48      | r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_8791,c_7021]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_9,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 23.23/3.48      inference(cnf_transformation,[],[f89]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1889,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_3405,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_0,c_1889]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_6307,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),sK1) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_6007,c_3405]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_12,plain,
% 23.23/3.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 23.23/3.48      inference(cnf_transformation,[],[f91]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1886,plain,
% 23.23/3.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_3101,plain,
% 23.23/3.48      ( r1_xboole_0(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_2006,c_1886]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_4514,plain,
% 23.23/3.48      ( r1_xboole_0(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_3101,c_1896]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7037,plain,
% 23.23/3.48      ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
% 23.23/3.48      inference(demodulation,[status(thm)],[c_6627,c_4514]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_31,negated_conjecture,
% 23.23/3.48      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 23.23/3.48      | r1_tarski(sK2,sK3) ),
% 23.23/3.48      inference(cnf_transformation,[],[f87]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1873,plain,
% 23.23/3.48      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7019,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.23/3.48      inference(demodulation,[status(thm)],[c_6616,c_1873]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7022,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) = iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.23/3.48      inference(light_normalisation,[status(thm)],[c_7019,c_6627]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_10,plain,
% 23.23/3.48      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.23/3.48      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 23.23/3.48      inference(cnf_transformation,[],[f90]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1888,plain,
% 23.23/3.48      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 23.23/3.48      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7779,plain,
% 23.23/3.48      ( r1_tarski(k5_xboole_0(sK1,sK3),X0) != iProver_top
% 23.23/3.48      | r1_tarski(sK1,k2_xboole_0(sK3,X0)) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_6309,c_1888]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_61920,plain,
% 23.23/3.48      ( r1_tarski(sK2,sK3) = iProver_top
% 23.23/3.48      | r1_tarski(sK1,k2_xboole_0(sK3,k5_xboole_0(sK1,sK2))) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_7022,c_7779]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_7,plain,
% 23.23/3.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 23.23/3.48      inference(cnf_transformation,[],[f62]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1891,plain,
% 23.23/3.48      ( r1_tarski(X0,X1) != iProver_top
% 23.23/3.48      | r1_tarski(X1,X2) != iProver_top
% 23.23/3.48      | r1_tarski(X0,X2) = iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_8093,plain,
% 23.23/3.48      ( r1_tarski(sK2,X0) = iProver_top
% 23.23/3.48      | r1_tarski(sK1,X0) != iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_5417,c_1891]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_62845,plain,
% 23.23/3.48      ( r1_tarski(sK2,k2_xboole_0(sK3,k5_xboole_0(sK1,sK2))) = iProver_top
% 23.23/3.48      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_61920,c_8093]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_11,plain,
% 23.23/3.48      ( r1_tarski(X0,X1)
% 23.23/3.48      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.23/3.48      | ~ r1_xboole_0(X0,X2) ),
% 23.23/3.48      inference(cnf_transformation,[],[f66]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_1887,plain,
% 23.23/3.48      ( r1_tarski(X0,X1) = iProver_top
% 23.23/3.48      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 23.23/3.48      | r1_xboole_0(X0,X2) != iProver_top ),
% 23.23/3.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_63476,plain,
% 23.23/3.48      ( r1_tarski(sK2,sK3) = iProver_top
% 23.23/3.48      | r1_xboole_0(sK2,k5_xboole_0(sK1,sK2)) != iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_62845,c_1887]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_91786,plain,
% 23.23/3.48      ( r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 23.23/3.48      inference(global_propositional_subsumption,
% 23.23/3.48                [status(thm)],
% 23.23/3.48                [c_91215,c_6307,c_7037,c_63476]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(c_91790,plain,
% 23.23/3.48      ( r1_tarski(sK2,sK3) != iProver_top ),
% 23.23/3.48      inference(superposition,[status(thm)],[c_9365,c_91786]) ).
% 23.23/3.48  
% 23.23/3.48  cnf(contradiction,plain,
% 23.23/3.48      ( $false ),
% 23.23/3.48      inference(minisat,[status(thm)],[c_91790,c_63476,c_7037]) ).
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.23/3.48  
% 23.23/3.48  ------                               Statistics
% 23.23/3.48  
% 23.23/3.48  ------ General
% 23.23/3.48  
% 23.23/3.48  abstr_ref_over_cycles:                  0
% 23.23/3.48  abstr_ref_under_cycles:                 0
% 23.23/3.48  gc_basic_clause_elim:                   0
% 23.23/3.48  forced_gc_time:                         0
% 23.23/3.48  parsing_time:                           0.011
% 23.23/3.48  unif_index_cands_time:                  0.
% 23.23/3.48  unif_index_add_time:                    0.
% 23.23/3.48  orderings_time:                         0.
% 23.23/3.48  out_proof_time:                         0.019
% 23.23/3.48  total_time:                             2.567
% 23.23/3.48  num_of_symbols:                         46
% 23.23/3.48  num_of_terms:                           110598
% 23.23/3.48  
% 23.23/3.48  ------ Preprocessing
% 23.23/3.48  
% 23.23/3.48  num_of_splits:                          0
% 23.23/3.48  num_of_split_atoms:                     0
% 23.23/3.48  num_of_reused_defs:                     0
% 23.23/3.48  num_eq_ax_congr_red:                    19
% 23.23/3.48  num_of_sem_filtered_clauses:            1
% 23.23/3.48  num_of_subtypes:                        0
% 23.23/3.48  monotx_restored_types:                  0
% 23.23/3.48  sat_num_of_epr_types:                   0
% 23.23/3.48  sat_num_of_non_cyclic_types:            0
% 23.23/3.48  sat_guarded_non_collapsed_types:        0
% 23.23/3.48  num_pure_diseq_elim:                    0
% 23.23/3.48  simp_replaced_by:                       0
% 23.23/3.48  res_preprocessed:                       144
% 23.23/3.48  prep_upred:                             0
% 23.23/3.48  prep_unflattend:                        76
% 23.23/3.48  smt_new_axioms:                         0
% 23.23/3.48  pred_elim_cands:                        3
% 23.23/3.48  pred_elim:                              2
% 23.23/3.48  pred_elim_cl:                           3
% 23.23/3.48  pred_elim_cycles:                       4
% 23.23/3.48  merged_defs:                            24
% 23.23/3.48  merged_defs_ncl:                        0
% 23.23/3.48  bin_hyper_res:                          25
% 23.23/3.48  prep_cycles:                            4
% 23.23/3.48  pred_elim_time:                         0.01
% 23.23/3.48  splitting_time:                         0.
% 23.23/3.48  sem_filter_time:                        0.
% 23.23/3.48  monotx_time:                            0.001
% 23.23/3.48  subtype_inf_time:                       0.
% 23.23/3.48  
% 23.23/3.48  ------ Problem properties
% 23.23/3.48  
% 23.23/3.48  clauses:                                30
% 23.23/3.48  conjectures:                            2
% 23.23/3.48  epr:                                    4
% 23.23/3.48  horn:                                   28
% 23.23/3.48  ground:                                 4
% 23.23/3.48  unary:                                  8
% 23.23/3.48  binary:                                 16
% 23.23/3.48  lits:                                   58
% 23.23/3.48  lits_eq:                                11
% 23.23/3.48  fd_pure:                                0
% 23.23/3.48  fd_pseudo:                              0
% 23.23/3.48  fd_cond:                                0
% 23.23/3.48  fd_pseudo_cond:                         3
% 23.23/3.48  ac_symbols:                             0
% 23.23/3.48  
% 23.23/3.48  ------ Propositional Solver
% 23.23/3.48  
% 23.23/3.48  prop_solver_calls:                      49
% 23.23/3.48  prop_fast_solver_calls:                 2215
% 23.23/3.48  smt_solver_calls:                       0
% 23.23/3.48  smt_fast_solver_calls:                  0
% 23.23/3.48  prop_num_of_clauses:                    42882
% 23.23/3.48  prop_preprocess_simplified:             58355
% 23.23/3.48  prop_fo_subsumed:                       150
% 23.23/3.48  prop_solver_time:                       0.
% 23.23/3.48  smt_solver_time:                        0.
% 23.23/3.48  smt_fast_solver_time:                   0.
% 23.23/3.48  prop_fast_solver_time:                  0.
% 23.23/3.48  prop_unsat_core_time:                   0.004
% 23.23/3.48  
% 23.23/3.48  ------ QBF
% 23.23/3.48  
% 23.23/3.48  qbf_q_res:                              0
% 23.23/3.48  qbf_num_tautologies:                    0
% 23.23/3.48  qbf_prep_cycles:                        0
% 23.23/3.48  
% 23.23/3.48  ------ BMC1
% 23.23/3.48  
% 23.23/3.48  bmc1_current_bound:                     -1
% 23.23/3.48  bmc1_last_solved_bound:                 -1
% 23.23/3.48  bmc1_unsat_core_size:                   -1
% 23.23/3.48  bmc1_unsat_core_parents_size:           -1
% 23.23/3.48  bmc1_merge_next_fun:                    0
% 23.23/3.48  bmc1_unsat_core_clauses_time:           0.
% 23.23/3.48  
% 23.23/3.48  ------ Instantiation
% 23.23/3.48  
% 23.23/3.48  inst_num_of_clauses:                    449
% 23.23/3.48  inst_num_in_passive:                    109
% 23.23/3.48  inst_num_in_active:                     2485
% 23.23/3.48  inst_num_in_unprocessed:                174
% 23.23/3.48  inst_num_of_loops:                      3169
% 23.23/3.48  inst_num_of_learning_restarts:          1
% 23.23/3.48  inst_num_moves_active_passive:          681
% 23.23/3.48  inst_lit_activity:                      0
% 23.23/3.48  inst_lit_activity_moves:                0
% 23.23/3.48  inst_num_tautologies:                   0
% 23.23/3.48  inst_num_prop_implied:                  0
% 23.23/3.48  inst_num_existing_simplified:           0
% 23.23/3.48  inst_num_eq_res_simplified:             0
% 23.23/3.48  inst_num_child_elim:                    0
% 23.23/3.48  inst_num_of_dismatching_blockings:      10024
% 23.23/3.48  inst_num_of_non_proper_insts:           10276
% 23.23/3.48  inst_num_of_duplicates:                 0
% 23.23/3.48  inst_inst_num_from_inst_to_res:         0
% 23.23/3.48  inst_dismatching_checking_time:         0.
% 23.23/3.48  
% 23.23/3.48  ------ Resolution
% 23.23/3.48  
% 23.23/3.48  res_num_of_clauses:                     40
% 23.23/3.48  res_num_in_passive:                     40
% 23.23/3.48  res_num_in_active:                      0
% 23.23/3.48  res_num_of_loops:                       148
% 23.23/3.48  res_forward_subset_subsumed:            538
% 23.23/3.48  res_backward_subset_subsumed:           30
% 23.23/3.48  res_forward_subsumed:                   3
% 23.23/3.48  res_backward_subsumed:                  0
% 23.23/3.48  res_forward_subsumption_resolution:     1
% 23.23/3.48  res_backward_subsumption_resolution:    0
% 23.23/3.48  res_clause_to_clause_subsumption:       29393
% 23.23/3.48  res_orphan_elimination:                 0
% 23.23/3.48  res_tautology_del:                      771
% 23.23/3.48  res_num_eq_res_simplified:              0
% 23.23/3.48  res_num_sel_changes:                    0
% 23.23/3.48  res_moves_from_active_to_pass:          0
% 23.23/3.48  
% 23.23/3.48  ------ Superposition
% 23.23/3.48  
% 23.23/3.48  sup_time_total:                         0.
% 23.23/3.48  sup_time_generating:                    0.
% 23.23/3.48  sup_time_sim_full:                      0.
% 23.23/3.48  sup_time_sim_immed:                     0.
% 23.23/3.48  
% 23.23/3.48  sup_num_of_clauses:                     4466
% 23.23/3.48  sup_num_in_active:                      539
% 23.23/3.48  sup_num_in_passive:                     3927
% 23.23/3.48  sup_num_of_loops:                       633
% 23.23/3.48  sup_fw_superposition:                   6794
% 23.23/3.48  sup_bw_superposition:                   4406
% 23.23/3.48  sup_immediate_simplified:               3360
% 23.23/3.48  sup_given_eliminated:                   1
% 23.23/3.48  comparisons_done:                       0
% 23.23/3.48  comparisons_avoided:                    61
% 23.23/3.48  
% 23.23/3.48  ------ Simplifications
% 23.23/3.48  
% 23.23/3.48  
% 23.23/3.48  sim_fw_subset_subsumed:                 153
% 23.23/3.48  sim_bw_subset_subsumed:                 183
% 23.23/3.48  sim_fw_subsumed:                        568
% 23.23/3.48  sim_bw_subsumed:                        39
% 23.23/3.48  sim_fw_subsumption_res:                 0
% 23.23/3.48  sim_bw_subsumption_res:                 0
% 23.23/3.48  sim_tautology_del:                      66
% 23.23/3.48  sim_eq_tautology_del:                   184
% 23.23/3.48  sim_eq_res_simp:                        0
% 23.23/3.48  sim_fw_demodulated:                     783
% 23.23/3.48  sim_bw_demodulated:                     74
% 23.23/3.48  sim_light_normalised:                   2188
% 23.23/3.48  sim_joinable_taut:                      0
% 23.23/3.48  sim_joinable_simp:                      0
% 23.23/3.48  sim_ac_normalised:                      0
% 23.23/3.48  sim_smt_subsumption:                    0
% 23.23/3.48  
%------------------------------------------------------------------------------
