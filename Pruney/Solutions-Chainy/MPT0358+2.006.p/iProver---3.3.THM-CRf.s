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
% DateTime   : Thu Dec  3 11:39:49 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 312 expanded)
%              Number of clauses        :   63 ( 105 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  432 (1080 expanded)
%              Number of equality atoms :  139 ( 342 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK3) != sK4
        | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
      & ( k1_subset_1(sK3) = sK4
        | r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k1_subset_1(sK3) != sK4
      | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
    & ( k1_subset_1(sK3) = sK4
      | r1_tarski(sK4,k3_subset_1(sK3,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f41])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f70,f58])).

fof(f73,plain,
    ( k1_subset_1(sK3) = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(definition_unfolding,[],[f73,f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( k1_subset_1(sK3) != sK4
    | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,
    ( k1_xboole_0 != sK4
    | ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(definition_unfolding,[],[f74,f69])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2335,plain,
    ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
    | r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6925,plain,
    ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
    | r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_2335])).

cnf(c_6930,plain,
    ( r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
    | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4)
    | ~ r1_tarski(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_6925])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6894,plain,
    ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
    | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6900,plain,
    ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
    | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_6894])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_408,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_409,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_415,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_409,c_26])).

cnf(c_1198,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1201,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1640,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1201])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1206,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1985,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_1640,c_1206])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_421,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_422,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1388,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_422])).

cnf(c_1440,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)) = k3_subset_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_0,c_1388])).

cnf(c_2131,plain,
    ( k3_subset_1(sK3,sK4) = k5_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1985,c_1440])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1199,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2137,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k5_xboole_0(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2131,c_1199])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1208,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3088,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK3,sK4))) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2137,c_1208])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1211,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3990,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_1211])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1205,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2459,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1205])).

cnf(c_3824,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k5_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_2459])).

cnf(c_4215,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3990,c_2137,c_3824])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3444,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_664,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1545,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_2487,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_3443,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2487])).

cnf(c_1462,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_1872,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | ~ r1_tarski(X2,k1_xboole_0)
    | X0 != X2
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1874,plain,
    ( r1_tarski(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
    | ~ r1_tarski(sK4,k1_xboole_0)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)) != k1_xboole_0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_661,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1554,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_662,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1438,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1553,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1392,plain,
    ( r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4)
    | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_74,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK4,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(sK4,k3_subset_1(sK3,sK4))
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6930,c_6900,c_4215,c_3444,c_3443,c_1874,c_1554,c_1553,c_1392,c_78,c_74,c_71,c_27])).

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
% 0.13/0.35  % DateTime   : Tue Dec  1 18:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.08/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.99  
% 2.08/0.99  ------  iProver source info
% 2.08/0.99  
% 2.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.99  git: non_committed_changes: false
% 2.08/0.99  git: last_make_outside_of_git: false
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     num_symb
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       true
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  ------ Parsing...
% 2.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.99  ------ Proving...
% 2.08/0.99  ------ Problem Properties 
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  clauses                                 25
% 2.08/0.99  conjectures                             2
% 2.08/0.99  EPR                                     3
% 2.08/0.99  Horn                                    18
% 2.08/0.99  unary                                   3
% 2.08/0.99  binary                                  14
% 2.08/0.99  lits                                    56
% 2.08/0.99  lits eq                                 16
% 2.08/0.99  fd_pure                                 0
% 2.08/0.99  fd_pseudo                               0
% 2.08/0.99  fd_cond                                 1
% 2.08/0.99  fd_pseudo_cond                          6
% 2.08/0.99  AC symbols                              0
% 2.08/0.99  
% 2.08/0.99  ------ Schedule dynamic 5 is on 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  Current options:
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     none
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       false
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ Proving...
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  % SZS status Theorem for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  fof(f2,axiom,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f16,plain,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f2])).
% 2.08/0.99  
% 2.08/0.99  fof(f22,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(nnf_transformation,[],[f16])).
% 2.08/0.99  
% 2.08/0.99  fof(f23,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(rectify,[],[f22])).
% 2.08/0.99  
% 2.08/0.99  fof(f24,plain,(
% 2.08/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f25,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.08/0.99  
% 2.08/0.99  fof(f44,plain,(
% 2.08/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f25])).
% 2.08/0.99  
% 2.08/0.99  fof(f3,axiom,(
% 2.08/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f26,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.08/0.99    inference(nnf_transformation,[],[f3])).
% 2.08/0.99  
% 2.08/0.99  fof(f27,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.08/0.99    inference(flattening,[],[f26])).
% 2.08/0.99  
% 2.08/0.99  fof(f28,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.08/0.99    inference(rectify,[],[f27])).
% 2.08/0.99  
% 2.08/0.99  fof(f29,plain,(
% 2.08/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f30,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 2.08/0.99  
% 2.08/0.99  fof(f48,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.08/0.99    inference(cnf_transformation,[],[f30])).
% 2.08/0.99  
% 2.08/0.99  fof(f6,axiom,(
% 2.08/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f58,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.99    inference(cnf_transformation,[],[f6])).
% 2.08/0.99  
% 2.08/0.99  fof(f79,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.08/0.99    inference(definition_unfolding,[],[f48,f58])).
% 2.08/0.99  
% 2.08/0.99  fof(f88,plain,(
% 2.08/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.08/0.99    inference(equality_resolution,[],[f79])).
% 2.08/0.99  
% 2.08/0.99  fof(f10,axiom,(
% 2.08/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f19,plain,(
% 2.08/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f10])).
% 2.08/0.99  
% 2.08/0.99  fof(f38,plain,(
% 2.08/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.08/0.99    inference(nnf_transformation,[],[f19])).
% 2.08/0.99  
% 2.08/0.99  fof(f65,plain,(
% 2.08/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f38])).
% 2.08/0.99  
% 2.08/0.99  fof(f14,conjecture,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f15,negated_conjecture,(
% 2.08/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.08/0.99    inference(negated_conjecture,[],[f14])).
% 2.08/0.99  
% 2.08/0.99  fof(f21,plain,(
% 2.08/0.99    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f15])).
% 2.08/0.99  
% 2.08/0.99  fof(f39,plain,(
% 2.08/0.99    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.99    inference(nnf_transformation,[],[f21])).
% 2.08/0.99  
% 2.08/0.99  fof(f40,plain,(
% 2.08/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.99    inference(flattening,[],[f39])).
% 2.08/0.99  
% 2.08/0.99  fof(f41,plain,(
% 2.08/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))) & (k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f42,plain,(
% 2.08/0.99    (k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))) & (k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f41])).
% 2.08/0.99  
% 2.08/0.99  fof(f72,plain,(
% 2.08/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f13,axiom,(
% 2.08/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f71,plain,(
% 2.08/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.08/0.99    inference(cnf_transformation,[],[f13])).
% 2.08/0.99  
% 2.08/0.99  fof(f9,axiom,(
% 2.08/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f34,plain,(
% 2.08/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.08/0.99    inference(nnf_transformation,[],[f9])).
% 2.08/0.99  
% 2.08/0.99  fof(f35,plain,(
% 2.08/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.08/0.99    inference(rectify,[],[f34])).
% 2.08/0.99  
% 2.08/0.99  fof(f36,plain,(
% 2.08/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f37,plain,(
% 2.08/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.08/0.99  
% 2.08/0.99  fof(f61,plain,(
% 2.08/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.08/0.99    inference(cnf_transformation,[],[f37])).
% 2.08/0.99  
% 2.08/0.99  fof(f93,plain,(
% 2.08/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.08/0.99    inference(equality_resolution,[],[f61])).
% 2.08/0.99  
% 2.08/0.99  fof(f7,axiom,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f17,plain,(
% 2.08/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.08/0.99    inference(ennf_transformation,[],[f7])).
% 2.08/0.99  
% 2.08/0.99  fof(f59,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f17])).
% 2.08/0.99  
% 2.08/0.99  fof(f1,axiom,(
% 2.08/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f43,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f1])).
% 2.08/0.99  
% 2.08/0.99  fof(f12,axiom,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f20,plain,(
% 2.08/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f12])).
% 2.08/0.99  
% 2.08/0.99  fof(f70,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.99    inference(cnf_transformation,[],[f20])).
% 2.08/0.99  
% 2.08/0.99  fof(f84,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.99    inference(definition_unfolding,[],[f70,f58])).
% 2.08/0.99  
% 2.08/0.99  fof(f73,plain,(
% 2.08/0.99    k1_subset_1(sK3) = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f11,axiom,(
% 2.08/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f69,plain,(
% 2.08/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f11])).
% 2.08/0.99  
% 2.08/0.99  fof(f86,plain,(
% 2.08/0.99    k1_xboole_0 = sK4 | r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 2.08/0.99    inference(definition_unfolding,[],[f73,f69])).
% 2.08/0.99  
% 2.08/0.99  fof(f5,axiom,(
% 2.08/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f33,plain,(
% 2.08/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.08/0.99    inference(nnf_transformation,[],[f5])).
% 2.08/0.99  
% 2.08/0.99  fof(f57,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f33])).
% 2.08/0.99  
% 2.08/0.99  fof(f81,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f57,f58])).
% 2.08/0.99  
% 2.08/0.99  fof(f47,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.08/0.99    inference(cnf_transformation,[],[f30])).
% 2.08/0.99  
% 2.08/0.99  fof(f80,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.08/0.99    inference(definition_unfolding,[],[f47,f58])).
% 2.08/0.99  
% 2.08/0.99  fof(f89,plain,(
% 2.08/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.08/0.99    inference(equality_resolution,[],[f80])).
% 2.08/0.99  
% 2.08/0.99  fof(f8,axiom,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f18,plain,(
% 2.08/0.99    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f8])).
% 2.08/0.99  
% 2.08/0.99  fof(f60,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.08/0.99    inference(cnf_transformation,[],[f18])).
% 2.08/0.99  
% 2.08/0.99  fof(f83,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.08/0.99    inference(definition_unfolding,[],[f60,f58])).
% 2.08/0.99  
% 2.08/0.99  fof(f4,axiom,(
% 2.08/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f31,plain,(
% 2.08/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.99    inference(nnf_transformation,[],[f4])).
% 2.08/0.99  
% 2.08/0.99  fof(f32,plain,(
% 2.08/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.99    inference(flattening,[],[f31])).
% 2.08/0.99  
% 2.08/0.99  fof(f53,plain,(
% 2.08/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.08/0.99    inference(cnf_transformation,[],[f32])).
% 2.08/0.99  
% 2.08/0.99  fof(f91,plain,(
% 2.08/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.08/0.99    inference(equality_resolution,[],[f53])).
% 2.08/0.99  
% 2.08/0.99  fof(f45,plain,(
% 2.08/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f25])).
% 2.08/0.99  
% 2.08/0.99  fof(f55,plain,(
% 2.08/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f32])).
% 2.08/0.99  
% 2.08/0.99  fof(f74,plain,(
% 2.08/0.99    k1_subset_1(sK3) != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f85,plain,(
% 2.08/0.99    k1_xboole_0 != sK4 | ~r1_tarski(sK4,k3_subset_1(sK3,sK4))),
% 2.08/0.99    inference(definition_unfolding,[],[f74,f69])).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.08/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2335,plain,
% 2.08/0.99      ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
% 2.08/0.99      | r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X1)
% 2.08/0.99      | ~ r1_tarski(X0,X1) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6925,plain,
% 2.08/0.99      ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
% 2.08/0.99      | r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 2.08/0.99      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_2335]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6930,plain,
% 2.08/0.99      ( r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
% 2.08/0.99      | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4)
% 2.08/0.99      | ~ r1_tarski(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_6925]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_8,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,X1)
% 2.08/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.08/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6894,plain,
% 2.08/0.99      ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),X0)
% 2.08/0.99      | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6900,plain,
% 2.08/0.99      ( ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
% 2.08/0.99      | ~ r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_6894]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_24,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_29,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_408,plain,
% 2.08/0.99      ( r2_hidden(X0,X1)
% 2.08/0.99      | v1_xboole_0(X1)
% 2.08/0.99      | k1_zfmisc_1(sK3) != X1
% 2.08/0.99      | sK4 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_409,plain,
% 2.08/0.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_26,plain,
% 2.08/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_415,plain,
% 2.08/0.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
% 2.08/0.99      inference(forward_subsumption_resolution,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_409,c_26]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1198,plain,
% 2.08/0.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_20,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1201,plain,
% 2.08/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.08/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1640,plain,
% 2.08/0.99      ( r1_tarski(sK4,sK3) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1198,c_1201]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_15,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.08/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1206,plain,
% 2.08/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1985,plain,
% 2.08/0.99      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1640,c_1206]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_0,plain,
% 2.08/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_25,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.08/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_421,plain,
% 2.08/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.08/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 2.08/0.99      | sK4 != X1 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_422,plain,
% 2.08/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 2.08/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1388,plain,
% 2.08/0.99      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 2.08/0.99      inference(equality_resolution,[status(thm)],[c_422]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1440,plain,
% 2.08/0.99      ( k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)) = k3_subset_1(sK3,sK4) ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_0,c_1388]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2131,plain,
% 2.08/0.99      ( k3_subset_1(sK3,sK4) = k5_xboole_0(sK3,sK4) ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_1985,c_1440]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_28,negated_conjecture,
% 2.08/0.99      ( r1_tarski(sK4,k3_subset_1(sK3,sK4)) | k1_xboole_0 = sK4 ),
% 2.08/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1199,plain,
% 2.08/0.99      ( k1_xboole_0 = sK4
% 2.08/0.99      | r1_tarski(sK4,k3_subset_1(sK3,sK4)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2137,plain,
% 2.08/0.99      ( sK4 = k1_xboole_0
% 2.08/0.99      | r1_tarski(sK4,k5_xboole_0(sK3,sK4)) = iProver_top ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_2131,c_1199]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_13,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1)
% 2.08/0.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.08/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1208,plain,
% 2.08/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 2.08/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3088,plain,
% 2.08/0.99      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK3,sK4))) = k1_xboole_0
% 2.08/0.99      | sK4 = k1_xboole_0 ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2137,c_1208]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_9,plain,
% 2.08/0.99      ( r2_hidden(X0,X1)
% 2.08/0.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.08/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1211,plain,
% 2.08/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.08/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3990,plain,
% 2.08/0.99      ( sK4 = k1_xboole_0
% 2.08/0.99      | r2_hidden(X0,sK4) = iProver_top
% 2.08/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_3088,c_1211]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_16,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
% 2.08/0.99      | k1_xboole_0 = X0 ),
% 2.08/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1205,plain,
% 2.08/0.99      ( k1_xboole_0 = X0
% 2.08/0.99      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2459,plain,
% 2.08/0.99      ( k1_xboole_0 = X0
% 2.08/0.99      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_0,c_1205]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3824,plain,
% 2.08/0.99      ( sK4 = k1_xboole_0
% 2.08/0.99      | r1_tarski(sK4,k5_xboole_0(sK3,sK4)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1985,c_2459]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4215,plain,
% 2.08/0.99      ( sK4 = k1_xboole_0 ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_3990,c_2137,c_3824]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_12,plain,
% 2.08/0.99      ( r1_tarski(X0,X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3444,plain,
% 2.08/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_664,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.08/0.99      theory(equality) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1545,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1)
% 2.08/0.99      | r1_tarski(sK4,k1_xboole_0)
% 2.08/0.99      | sK4 != X0
% 2.08/0.99      | k1_xboole_0 != X1 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_664]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2487,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.08/0.99      | r1_tarski(sK4,k1_xboole_0)
% 2.08/0.99      | sK4 != X0
% 2.08/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1545]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3443,plain,
% 2.08/0.99      ( r1_tarski(sK4,k1_xboole_0)
% 2.08/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.08/0.99      | sK4 != k1_xboole_0
% 2.08/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_2487]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1462,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1)
% 2.08/0.99      | r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
% 2.08/0.99      | X2 != X0
% 2.08/0.99      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) != X1 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_664]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1872,plain,
% 2.08/0.99      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
% 2.08/0.99      | ~ r1_tarski(X2,k1_xboole_0)
% 2.08/0.99      | X0 != X2
% 2.08/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) != k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1874,plain,
% 2.08/0.99      ( r1_tarski(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))
% 2.08/0.99      | ~ r1_tarski(sK4,k1_xboole_0)
% 2.08/0.99      | k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)) != k1_xboole_0
% 2.08/0.99      | sK4 != sK4 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1872]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_661,plain,( X0 = X0 ),theory(equality) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1554,plain,
% 2.08/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_661]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_662,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1438,plain,
% 2.08/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_662]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1553,plain,
% 2.08/0.99      ( sK4 != k1_xboole_0
% 2.08/0.99      | k1_xboole_0 = sK4
% 2.08/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1438]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2,plain,
% 2.08/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1392,plain,
% 2.08/0.99      ( r2_hidden(sK0(sK4,k3_subset_1(sK3,sK4)),sK4)
% 2.08/0.99      | r1_tarski(sK4,k3_subset_1(sK3,sK4)) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_10,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.08/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_78,plain,
% 2.08/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_74,plain,
% 2.08/0.99      ( r1_tarski(sK4,sK4) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_71,plain,
% 2.08/0.99      ( ~ r1_tarski(sK4,sK4)
% 2.08/0.99      | k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)) = k1_xboole_0 ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_27,negated_conjecture,
% 2.08/0.99      ( ~ r1_tarski(sK4,k3_subset_1(sK3,sK4)) | k1_xboole_0 != sK4 ),
% 2.08/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(contradiction,plain,
% 2.08/0.99      ( $false ),
% 2.08/0.99      inference(minisat,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_6930,c_6900,c_4215,c_3444,c_3443,c_1874,c_1554,c_1553,
% 2.08/0.99                 c_1392,c_78,c_74,c_71,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  ------                               Statistics
% 2.08/0.99  
% 2.08/0.99  ------ General
% 2.08/0.99  
% 2.08/0.99  abstr_ref_over_cycles:                  0
% 2.08/0.99  abstr_ref_under_cycles:                 0
% 2.08/0.99  gc_basic_clause_elim:                   0
% 2.08/0.99  forced_gc_time:                         0
% 2.08/0.99  parsing_time:                           0.012
% 2.08/0.99  unif_index_cands_time:                  0.
% 2.08/0.99  unif_index_add_time:                    0.
% 2.08/0.99  orderings_time:                         0.
% 2.08/0.99  out_proof_time:                         0.009
% 2.08/0.99  total_time:                             0.218
% 2.08/0.99  num_of_symbols:                         45
% 2.08/0.99  num_of_terms:                           8203
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing
% 2.08/0.99  
% 2.08/0.99  num_of_splits:                          0
% 2.08/0.99  num_of_split_atoms:                     0
% 2.08/0.99  num_of_reused_defs:                     0
% 2.08/0.99  num_eq_ax_congr_red:                    28
% 2.08/0.99  num_of_sem_filtered_clauses:            1
% 2.08/0.99  num_of_subtypes:                        0
% 2.08/0.99  monotx_restored_types:                  0
% 2.08/0.99  sat_num_of_epr_types:                   0
% 2.08/0.99  sat_num_of_non_cyclic_types:            0
% 2.08/0.99  sat_guarded_non_collapsed_types:        0
% 2.08/0.99  num_pure_diseq_elim:                    0
% 2.08/0.99  simp_replaced_by:                       0
% 2.08/0.99  res_preprocessed:                       121
% 2.08/0.99  prep_upred:                             0
% 2.08/0.99  prep_unflattend:                        9
% 2.08/0.99  smt_new_axioms:                         0
% 2.08/0.99  pred_elim_cands:                        2
% 2.08/0.99  pred_elim:                              2
% 2.08/0.99  pred_elim_cl:                           4
% 2.08/0.99  pred_elim_cycles:                       4
% 2.08/0.99  merged_defs:                            24
% 2.08/0.99  merged_defs_ncl:                        0
% 2.08/0.99  bin_hyper_res:                          25
% 2.08/0.99  prep_cycles:                            4
% 2.08/0.99  pred_elim_time:                         0.001
% 2.08/0.99  splitting_time:                         0.
% 2.08/0.99  sem_filter_time:                        0.
% 2.08/0.99  monotx_time:                            0.
% 2.08/0.99  subtype_inf_time:                       0.
% 2.08/0.99  
% 2.08/0.99  ------ Problem properties
% 2.08/0.99  
% 2.08/0.99  clauses:                                25
% 2.08/0.99  conjectures:                            2
% 2.08/0.99  epr:                                    3
% 2.08/0.99  horn:                                   18
% 2.08/0.99  ground:                                 3
% 2.08/0.99  unary:                                  3
% 2.08/0.99  binary:                                 14
% 2.08/0.99  lits:                                   56
% 2.08/0.99  lits_eq:                                16
% 2.08/0.99  fd_pure:                                0
% 2.08/0.99  fd_pseudo:                              0
% 2.08/0.99  fd_cond:                                1
% 2.08/0.99  fd_pseudo_cond:                         6
% 2.08/0.99  ac_symbols:                             0
% 2.08/0.99  
% 2.08/0.99  ------ Propositional Solver
% 2.08/0.99  
% 2.08/0.99  prop_solver_calls:                      28
% 2.08/0.99  prop_fast_solver_calls:                 701
% 2.08/0.99  smt_solver_calls:                       0
% 2.08/0.99  smt_fast_solver_calls:                  0
% 2.08/0.99  prop_num_of_clauses:                    2865
% 2.08/0.99  prop_preprocess_simplified:             8423
% 2.08/0.99  prop_fo_subsumed:                       8
% 2.08/0.99  prop_solver_time:                       0.
% 2.08/0.99  smt_solver_time:                        0.
% 2.08/0.99  smt_fast_solver_time:                   0.
% 2.08/0.99  prop_fast_solver_time:                  0.
% 2.08/0.99  prop_unsat_core_time:                   0.
% 2.08/0.99  
% 2.08/0.99  ------ QBF
% 2.08/0.99  
% 2.08/0.99  qbf_q_res:                              0
% 2.08/0.99  qbf_num_tautologies:                    0
% 2.08/0.99  qbf_prep_cycles:                        0
% 2.08/0.99  
% 2.08/0.99  ------ BMC1
% 2.08/0.99  
% 2.08/0.99  bmc1_current_bound:                     -1
% 2.08/0.99  bmc1_last_solved_bound:                 -1
% 2.08/0.99  bmc1_unsat_core_size:                   -1
% 2.08/0.99  bmc1_unsat_core_parents_size:           -1
% 2.08/0.99  bmc1_merge_next_fun:                    0
% 2.08/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation
% 2.08/0.99  
% 2.08/0.99  inst_num_of_clauses:                    754
% 2.08/0.99  inst_num_in_passive:                    426
% 2.08/0.99  inst_num_in_active:                     177
% 2.08/0.99  inst_num_in_unprocessed:                150
% 2.08/0.99  inst_num_of_loops:                      309
% 2.08/0.99  inst_num_of_learning_restarts:          0
% 2.08/0.99  inst_num_moves_active_passive:          129
% 2.08/0.99  inst_lit_activity:                      0
% 2.08/0.99  inst_lit_activity_moves:                0
% 2.08/0.99  inst_num_tautologies:                   0
% 2.08/0.99  inst_num_prop_implied:                  0
% 2.08/0.99  inst_num_existing_simplified:           0
% 2.08/0.99  inst_num_eq_res_simplified:             0
% 2.08/0.99  inst_num_child_elim:                    0
% 2.08/0.99  inst_num_of_dismatching_blockings:      223
% 2.08/0.99  inst_num_of_non_proper_insts:           557
% 2.08/0.99  inst_num_of_duplicates:                 0
% 2.08/0.99  inst_inst_num_from_inst_to_res:         0
% 2.08/0.99  inst_dismatching_checking_time:         0.
% 2.08/0.99  
% 2.08/0.99  ------ Resolution
% 2.08/0.99  
% 2.08/0.99  res_num_of_clauses:                     0
% 2.08/0.99  res_num_in_passive:                     0
% 2.08/0.99  res_num_in_active:                      0
% 2.08/0.99  res_num_of_loops:                       125
% 2.08/0.99  res_forward_subset_subsumed:            18
% 2.08/0.99  res_backward_subset_subsumed:           0
% 2.08/0.99  res_forward_subsumed:                   2
% 2.08/0.99  res_backward_subsumed:                  0
% 2.08/0.99  res_forward_subsumption_resolution:     2
% 2.08/0.99  res_backward_subsumption_resolution:    0
% 2.08/0.99  res_clause_to_clause_subsumption:       495
% 2.08/0.99  res_orphan_elimination:                 0
% 2.08/0.99  res_tautology_del:                      70
% 2.08/0.99  res_num_eq_res_simplified:              0
% 2.08/0.99  res_num_sel_changes:                    0
% 2.08/0.99  res_moves_from_active_to_pass:          0
% 2.08/0.99  
% 2.08/0.99  ------ Superposition
% 2.08/0.99  
% 2.08/0.99  sup_time_total:                         0.
% 2.08/0.99  sup_time_generating:                    0.
% 2.08/0.99  sup_time_sim_full:                      0.
% 2.08/0.99  sup_time_sim_immed:                     0.
% 2.08/0.99  
% 2.08/0.99  sup_num_of_clauses:                     116
% 2.08/0.99  sup_num_in_active:                      37
% 2.08/0.99  sup_num_in_passive:                     79
% 2.08/0.99  sup_num_of_loops:                       60
% 2.08/0.99  sup_fw_superposition:                   91
% 2.08/0.99  sup_bw_superposition:                   77
% 2.08/0.99  sup_immediate_simplified:               11
% 2.08/0.99  sup_given_eliminated:                   0
% 2.08/0.99  comparisons_done:                       0
% 2.08/0.99  comparisons_avoided:                    18
% 2.08/0.99  
% 2.08/0.99  ------ Simplifications
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  sim_fw_subset_subsumed:                 5
% 2.08/0.99  sim_bw_subset_subsumed:                 6
% 2.08/0.99  sim_fw_subsumed:                        1
% 2.08/0.99  sim_bw_subsumed:                        2
% 2.08/0.99  sim_fw_subsumption_res:                 1
% 2.08/0.99  sim_bw_subsumption_res:                 0
% 2.08/0.99  sim_tautology_del:                      13
% 2.08/0.99  sim_eq_tautology_del:                   10
% 2.08/0.99  sim_eq_res_simp:                        2
% 2.08/0.99  sim_fw_demodulated:                     1
% 2.08/0.99  sim_bw_demodulated:                     21
% 2.08/0.99  sim_light_normalised:                   1
% 2.08/0.99  sim_joinable_taut:                      0
% 2.08/0.99  sim_joinable_simp:                      0
% 2.08/0.99  sim_ac_normalised:                      0
% 2.08/0.99  sim_smt_subsumption:                    0
% 2.08/0.99  
%------------------------------------------------------------------------------
