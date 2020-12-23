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
% DateTime   : Thu Dec  3 11:41:04 EST 2020

% Result     : Timeout 58.80s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  127 ( 198 expanded)
%              Number of clauses        :   69 (  77 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  488 (1000 expanded)
%              Number of equality atoms :  142 ( 214 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK6) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,sK6)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,sK6)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK4,X2) != sK5
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK5) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK5) ) )
              | ~ m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,k1_zfmisc_1(sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k3_subset_1(sK4,sK6) != sK5
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK6)
            | ~ r2_hidden(X3,sK5) )
          & ( r2_hidden(X3,sK6)
            | r2_hidden(X3,sK5) ) )
        | ~ m1_subset_1(X3,sK4) )
    & m1_subset_1(sK6,k1_zfmisc_1(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f34,f36,f35])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK6)
      | ~ r2_hidden(X3,sK5)
      | ~ m1_subset_1(X3,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK6)
      | r2_hidden(X3,sK5)
      | ~ m1_subset_1(X3,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    k3_subset_1(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_742,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_264039,plain,
    ( k3_subset_1(sK4,sK6) = k3_subset_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_743,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_223149,plain,
    ( k3_subset_1(sK4,sK6) != X0
    | k3_subset_1(sK4,sK6) = k5_xboole_0(X1,k3_xboole_0(X1,sK6))
    | k5_xboole_0(X1,k3_xboole_0(X1,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_264038,plain,
    ( k3_subset_1(sK4,sK6) != k3_subset_1(sK4,sK6)
    | k3_subset_1(sK4,sK6) = k5_xboole_0(X0,k3_xboole_0(X0,sK6))
    | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) != k3_subset_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_223149])).

cnf(c_264040,plain,
    ( k3_subset_1(sK4,sK6) != k3_subset_1(sK4,sK6)
    | k3_subset_1(sK4,sK6) = k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
    | k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) != k3_subset_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_264038])).

cnf(c_193709,plain,
    ( k3_subset_1(sK4,sK6) != X0
    | k3_subset_1(sK4,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_219667,plain,
    ( k3_subset_1(sK4,sK6) != k5_xboole_0(X0,k3_xboole_0(X0,sK6))
    | k3_subset_1(sK4,sK6) = sK5
    | sK5 != k5_xboole_0(X0,k3_xboole_0(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_193709])).

cnf(c_219668,plain,
    ( k3_subset_1(sK4,sK6) != k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
    | k3_subset_1(sK4,sK6) = sK5
    | sK5 != k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_219667])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X0)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14116,plain,
    ( ~ r2_hidden(sK2(X0,sK6,X1),X0)
    | ~ r2_hidden(sK2(X0,sK6,X1),X1)
    | r2_hidden(sK2(X0,sK6,X1),sK6)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = X1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_35433,plain,
    ( ~ r2_hidden(sK2(X0,sK6,sK5),X0)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
    | r2_hidden(sK2(X0,sK6,sK5),sK6)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_14116])).

cnf(c_35434,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5
    | r2_hidden(sK2(X0,sK6,sK5),X0) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35433])).

cnf(c_35436,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
    | r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK6) = iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35434])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_1])).

cnf(c_146,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK5)
    | ~ r2_hidden(X2,sK6)
    | X2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_22])).

cnf(c_540,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_2775,plain,
    ( ~ r2_hidden(sK2(X0,X1,sK5),sK5)
    | ~ r2_hidden(sK2(X0,X1,sK5),sK6)
    | ~ r2_hidden(sK2(X0,X1,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_19273,plain,
    ( ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK6)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_19274,plain,
    ( r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK6) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19273])).

cnf(c_19276,plain,
    ( r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK6) != iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19274])).

cnf(c_1709,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1820,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_15396,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) != sK5
    | sK5 = k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8362,plain,
    ( r2_hidden(sK2(sK4,sK6,sK5),sK5)
    | r2_hidden(sK2(sK4,sK6,sK5),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8365,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
    | r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8362])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1629,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8328,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
    | r2_hidden(sK2(X0,sK6,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_8329,plain,
    ( r1_tarski(sK5,sK4) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8328])).

cnf(c_8331,plain,
    ( r1_tarski(sK5,sK4) != iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8329])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK5)
    | r2_hidden(X0,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK5)
    | r2_hidden(X2,sK6)
    | X2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_23])).

cnf(c_525,plain,
    ( r2_hidden(X0,sK5)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_5259,plain,
    ( r2_hidden(sK2(X0,sK6,sK5),sK5)
    | r2_hidden(sK2(X0,sK6,sK5),sK6)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_5264,plain,
    ( r2_hidden(sK2(X0,sK6,sK5),sK5) = iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK6) = iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5259])).

cnf(c_5266,plain,
    ( r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK6) = iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5264])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2773,plain,
    ( ~ r2_hidden(sK2(X0,X1,sK5),X1)
    | r2_hidden(sK2(X0,X1,sK5),sK5)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5253,plain,
    ( r2_hidden(sK2(X0,sK6,sK5),sK5)
    | ~ r2_hidden(sK2(X0,sK6,sK5),sK6)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_5260,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5
    | r2_hidden(sK2(X0,sK6,sK5),sK5) = iProver_top
    | r2_hidden(sK2(X0,sK6,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5253])).

cnf(c_5262,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
    | r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
    | r2_hidden(sK2(sK4,sK6,sK5),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5260])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1907,plain,
    ( r1_tarski(sK5,sK4)
    | ~ r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1908,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK5,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_1821,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_759,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_749,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_756,plain,
    ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_626,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_627,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_628,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = k3_subset_1(sK4,sK6)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_608,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_609,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_610,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_36,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_21,negated_conjecture,
    ( k3_subset_1(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_264039,c_264040,c_219668,c_35436,c_19276,c_15396,c_8365,c_8331,c_5266,c_5262,c_1908,c_1821,c_759,c_756,c_628,c_610,c_36,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 58.80/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.80/8.00  
% 58.80/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 58.80/8.00  
% 58.80/8.00  ------  iProver source info
% 58.80/8.00  
% 58.80/8.00  git: date: 2020-06-30 10:37:57 +0100
% 58.80/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 58.80/8.00  git: non_committed_changes: false
% 58.80/8.00  git: last_make_outside_of_git: false
% 58.80/8.00  
% 58.80/8.00  ------ 
% 58.80/8.00  
% 58.80/8.00  ------ Input Options
% 58.80/8.00  
% 58.80/8.00  --out_options                           all
% 58.80/8.00  --tptp_safe_out                         true
% 58.80/8.00  --problem_path                          ""
% 58.80/8.00  --include_path                          ""
% 58.80/8.00  --clausifier                            res/vclausify_rel
% 58.80/8.00  --clausifier_options                    --mode clausify
% 58.80/8.00  --stdin                                 false
% 58.80/8.00  --stats_out                             all
% 58.80/8.00  
% 58.80/8.00  ------ General Options
% 58.80/8.00  
% 58.80/8.00  --fof                                   false
% 58.80/8.00  --time_out_real                         305.
% 58.80/8.00  --time_out_virtual                      -1.
% 58.80/8.00  --symbol_type_check                     false
% 58.80/8.00  --clausify_out                          false
% 58.80/8.00  --sig_cnt_out                           false
% 58.80/8.00  --trig_cnt_out                          false
% 58.80/8.00  --trig_cnt_out_tolerance                1.
% 58.80/8.00  --trig_cnt_out_sk_spl                   false
% 58.80/8.00  --abstr_cl_out                          false
% 58.80/8.00  
% 58.80/8.00  ------ Global Options
% 58.80/8.00  
% 58.80/8.00  --schedule                              default
% 58.80/8.00  --add_important_lit                     false
% 58.80/8.00  --prop_solver_per_cl                    1000
% 58.80/8.00  --min_unsat_core                        false
% 58.80/8.00  --soft_assumptions                      false
% 58.80/8.00  --soft_lemma_size                       3
% 58.80/8.00  --prop_impl_unit_size                   0
% 58.80/8.00  --prop_impl_unit                        []
% 58.80/8.00  --share_sel_clauses                     true
% 58.80/8.00  --reset_solvers                         false
% 58.80/8.00  --bc_imp_inh                            [conj_cone]
% 58.80/8.00  --conj_cone_tolerance                   3.
% 58.80/8.00  --extra_neg_conj                        none
% 58.80/8.00  --large_theory_mode                     true
% 58.80/8.00  --prolific_symb_bound                   200
% 58.80/8.00  --lt_threshold                          2000
% 58.80/8.00  --clause_weak_htbl                      true
% 58.80/8.00  --gc_record_bc_elim                     false
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing Options
% 58.80/8.00  
% 58.80/8.00  --preprocessing_flag                    true
% 58.80/8.00  --time_out_prep_mult                    0.1
% 58.80/8.00  --splitting_mode                        input
% 58.80/8.00  --splitting_grd                         true
% 58.80/8.00  --splitting_cvd                         false
% 58.80/8.00  --splitting_cvd_svl                     false
% 58.80/8.00  --splitting_nvd                         32
% 58.80/8.00  --sub_typing                            true
% 58.80/8.00  --prep_gs_sim                           true
% 58.80/8.00  --prep_unflatten                        true
% 58.80/8.00  --prep_res_sim                          true
% 58.80/8.00  --prep_upred                            true
% 58.80/8.00  --prep_sem_filter                       exhaustive
% 58.80/8.00  --prep_sem_filter_out                   false
% 58.80/8.00  --pred_elim                             true
% 58.80/8.00  --res_sim_input                         true
% 58.80/8.00  --eq_ax_congr_red                       true
% 58.80/8.00  --pure_diseq_elim                       true
% 58.80/8.00  --brand_transform                       false
% 58.80/8.00  --non_eq_to_eq                          false
% 58.80/8.00  --prep_def_merge                        true
% 58.80/8.00  --prep_def_merge_prop_impl              false
% 58.80/8.00  --prep_def_merge_mbd                    true
% 58.80/8.00  --prep_def_merge_tr_red                 false
% 58.80/8.00  --prep_def_merge_tr_cl                  false
% 58.80/8.00  --smt_preprocessing                     true
% 58.80/8.00  --smt_ac_axioms                         fast
% 58.80/8.00  --preprocessed_out                      false
% 58.80/8.00  --preprocessed_stats                    false
% 58.80/8.00  
% 58.80/8.00  ------ Abstraction refinement Options
% 58.80/8.00  
% 58.80/8.00  --abstr_ref                             []
% 58.80/8.00  --abstr_ref_prep                        false
% 58.80/8.00  --abstr_ref_until_sat                   false
% 58.80/8.00  --abstr_ref_sig_restrict                funpre
% 58.80/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 58.80/8.00  --abstr_ref_under                       []
% 58.80/8.00  
% 58.80/8.00  ------ SAT Options
% 58.80/8.00  
% 58.80/8.00  --sat_mode                              false
% 58.80/8.00  --sat_fm_restart_options                ""
% 58.80/8.00  --sat_gr_def                            false
% 58.80/8.00  --sat_epr_types                         true
% 58.80/8.00  --sat_non_cyclic_types                  false
% 58.80/8.00  --sat_finite_models                     false
% 58.80/8.00  --sat_fm_lemmas                         false
% 58.80/8.00  --sat_fm_prep                           false
% 58.80/8.00  --sat_fm_uc_incr                        true
% 58.80/8.00  --sat_out_model                         small
% 58.80/8.00  --sat_out_clauses                       false
% 58.80/8.00  
% 58.80/8.00  ------ QBF Options
% 58.80/8.00  
% 58.80/8.00  --qbf_mode                              false
% 58.80/8.00  --qbf_elim_univ                         false
% 58.80/8.00  --qbf_dom_inst                          none
% 58.80/8.00  --qbf_dom_pre_inst                      false
% 58.80/8.00  --qbf_sk_in                             false
% 58.80/8.00  --qbf_pred_elim                         true
% 58.80/8.00  --qbf_split                             512
% 58.80/8.00  
% 58.80/8.00  ------ BMC1 Options
% 58.80/8.00  
% 58.80/8.00  --bmc1_incremental                      false
% 58.80/8.00  --bmc1_axioms                           reachable_all
% 58.80/8.00  --bmc1_min_bound                        0
% 58.80/8.00  --bmc1_max_bound                        -1
% 58.80/8.00  --bmc1_max_bound_default                -1
% 58.80/8.00  --bmc1_symbol_reachability              true
% 58.80/8.00  --bmc1_property_lemmas                  false
% 58.80/8.00  --bmc1_k_induction                      false
% 58.80/8.00  --bmc1_non_equiv_states                 false
% 58.80/8.00  --bmc1_deadlock                         false
% 58.80/8.00  --bmc1_ucm                              false
% 58.80/8.00  --bmc1_add_unsat_core                   none
% 58.80/8.00  --bmc1_unsat_core_children              false
% 58.80/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 58.80/8.00  --bmc1_out_stat                         full
% 58.80/8.00  --bmc1_ground_init                      false
% 58.80/8.00  --bmc1_pre_inst_next_state              false
% 58.80/8.00  --bmc1_pre_inst_state                   false
% 58.80/8.00  --bmc1_pre_inst_reach_state             false
% 58.80/8.00  --bmc1_out_unsat_core                   false
% 58.80/8.00  --bmc1_aig_witness_out                  false
% 58.80/8.00  --bmc1_verbose                          false
% 58.80/8.00  --bmc1_dump_clauses_tptp                false
% 58.80/8.00  --bmc1_dump_unsat_core_tptp             false
% 58.80/8.00  --bmc1_dump_file                        -
% 58.80/8.00  --bmc1_ucm_expand_uc_limit              128
% 58.80/8.00  --bmc1_ucm_n_expand_iterations          6
% 58.80/8.00  --bmc1_ucm_extend_mode                  1
% 58.80/8.00  --bmc1_ucm_init_mode                    2
% 58.80/8.00  --bmc1_ucm_cone_mode                    none
% 58.80/8.00  --bmc1_ucm_reduced_relation_type        0
% 58.80/8.00  --bmc1_ucm_relax_model                  4
% 58.80/8.00  --bmc1_ucm_full_tr_after_sat            true
% 58.80/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 58.80/8.00  --bmc1_ucm_layered_model                none
% 58.80/8.00  --bmc1_ucm_max_lemma_size               10
% 58.80/8.00  
% 58.80/8.00  ------ AIG Options
% 58.80/8.00  
% 58.80/8.00  --aig_mode                              false
% 58.80/8.00  
% 58.80/8.00  ------ Instantiation Options
% 58.80/8.00  
% 58.80/8.00  --instantiation_flag                    true
% 58.80/8.00  --inst_sos_flag                         false
% 58.80/8.00  --inst_sos_phase                        true
% 58.80/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 58.80/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 58.80/8.00  --inst_lit_sel_side                     num_symb
% 58.80/8.00  --inst_solver_per_active                1400
% 58.80/8.00  --inst_solver_calls_frac                1.
% 58.80/8.00  --inst_passive_queue_type               priority_queues
% 58.80/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 58.80/8.00  --inst_passive_queues_freq              [25;2]
% 58.80/8.00  --inst_dismatching                      true
% 58.80/8.00  --inst_eager_unprocessed_to_passive     true
% 58.80/8.00  --inst_prop_sim_given                   true
% 58.80/8.00  --inst_prop_sim_new                     false
% 58.80/8.00  --inst_subs_new                         false
% 58.80/8.00  --inst_eq_res_simp                      false
% 58.80/8.00  --inst_subs_given                       false
% 58.80/8.00  --inst_orphan_elimination               true
% 58.80/8.00  --inst_learning_loop_flag               true
% 58.80/8.00  --inst_learning_start                   3000
% 58.80/8.00  --inst_learning_factor                  2
% 58.80/8.00  --inst_start_prop_sim_after_learn       3
% 58.80/8.00  --inst_sel_renew                        solver
% 58.80/8.00  --inst_lit_activity_flag                true
% 58.80/8.00  --inst_restr_to_given                   false
% 58.80/8.00  --inst_activity_threshold               500
% 58.80/8.00  --inst_out_proof                        true
% 58.80/8.00  
% 58.80/8.00  ------ Resolution Options
% 58.80/8.00  
% 58.80/8.00  --resolution_flag                       true
% 58.80/8.00  --res_lit_sel                           adaptive
% 58.80/8.00  --res_lit_sel_side                      none
% 58.80/8.00  --res_ordering                          kbo
% 58.80/8.00  --res_to_prop_solver                    active
% 58.80/8.00  --res_prop_simpl_new                    false
% 58.80/8.00  --res_prop_simpl_given                  true
% 58.80/8.00  --res_passive_queue_type                priority_queues
% 58.80/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 58.80/8.00  --res_passive_queues_freq               [15;5]
% 58.80/8.00  --res_forward_subs                      full
% 58.80/8.00  --res_backward_subs                     full
% 58.80/8.00  --res_forward_subs_resolution           true
% 58.80/8.00  --res_backward_subs_resolution          true
% 58.80/8.00  --res_orphan_elimination                true
% 58.80/8.00  --res_time_limit                        2.
% 58.80/8.00  --res_out_proof                         true
% 58.80/8.00  
% 58.80/8.00  ------ Superposition Options
% 58.80/8.00  
% 58.80/8.00  --superposition_flag                    true
% 58.80/8.00  --sup_passive_queue_type                priority_queues
% 58.80/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 58.80/8.00  --sup_passive_queues_freq               [8;1;4]
% 58.80/8.00  --demod_completeness_check              fast
% 58.80/8.00  --demod_use_ground                      true
% 58.80/8.00  --sup_to_prop_solver                    passive
% 58.80/8.00  --sup_prop_simpl_new                    true
% 58.80/8.00  --sup_prop_simpl_given                  true
% 58.80/8.00  --sup_fun_splitting                     false
% 58.80/8.00  --sup_smt_interval                      50000
% 58.80/8.00  
% 58.80/8.00  ------ Superposition Simplification Setup
% 58.80/8.00  
% 58.80/8.00  --sup_indices_passive                   []
% 58.80/8.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 58.80/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_full_bw                           [BwDemod]
% 58.80/8.00  --sup_immed_triv                        [TrivRules]
% 58.80/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 58.80/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_immed_bw_main                     []
% 58.80/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 58.80/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 58.80/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 58.80/8.00  
% 58.80/8.00  ------ Combination Options
% 58.80/8.00  
% 58.80/8.00  --comb_res_mult                         3
% 58.80/8.00  --comb_sup_mult                         2
% 58.80/8.00  --comb_inst_mult                        10
% 58.80/8.00  
% 58.80/8.00  ------ Debug Options
% 58.80/8.00  
% 58.80/8.00  --dbg_backtrace                         false
% 58.80/8.00  --dbg_dump_prop_clauses                 false
% 58.80/8.00  --dbg_dump_prop_clauses_file            -
% 58.80/8.00  --dbg_out_stat                          false
% 58.80/8.00  ------ Parsing...
% 58.80/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 58.80/8.00  ------ Proving...
% 58.80/8.00  ------ Problem Properties 
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  clauses                                 30
% 58.80/8.00  conjectures                             1
% 58.80/8.00  EPR                                     6
% 58.80/8.00  Horn                                    19
% 58.80/8.00  unary                                   4
% 58.80/8.00  binary                                  11
% 58.80/8.00  lits                                    74
% 58.80/8.00  lits eq                                 15
% 58.80/8.00  fd_pure                                 0
% 58.80/8.00  fd_pseudo                               0
% 58.80/8.00  fd_cond                                 0
% 58.80/8.00  fd_pseudo_cond                          5
% 58.80/8.00  AC symbols                              0
% 58.80/8.00  
% 58.80/8.00  ------ Schedule dynamic 5 is on 
% 58.80/8.00  
% 58.80/8.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  ------ 
% 58.80/8.00  Current options:
% 58.80/8.00  ------ 
% 58.80/8.00  
% 58.80/8.00  ------ Input Options
% 58.80/8.00  
% 58.80/8.00  --out_options                           all
% 58.80/8.00  --tptp_safe_out                         true
% 58.80/8.00  --problem_path                          ""
% 58.80/8.00  --include_path                          ""
% 58.80/8.00  --clausifier                            res/vclausify_rel
% 58.80/8.00  --clausifier_options                    --mode clausify
% 58.80/8.00  --stdin                                 false
% 58.80/8.00  --stats_out                             all
% 58.80/8.00  
% 58.80/8.00  ------ General Options
% 58.80/8.00  
% 58.80/8.00  --fof                                   false
% 58.80/8.00  --time_out_real                         305.
% 58.80/8.00  --time_out_virtual                      -1.
% 58.80/8.00  --symbol_type_check                     false
% 58.80/8.00  --clausify_out                          false
% 58.80/8.00  --sig_cnt_out                           false
% 58.80/8.00  --trig_cnt_out                          false
% 58.80/8.00  --trig_cnt_out_tolerance                1.
% 58.80/8.00  --trig_cnt_out_sk_spl                   false
% 58.80/8.00  --abstr_cl_out                          false
% 58.80/8.00  
% 58.80/8.00  ------ Global Options
% 58.80/8.00  
% 58.80/8.00  --schedule                              default
% 58.80/8.00  --add_important_lit                     false
% 58.80/8.00  --prop_solver_per_cl                    1000
% 58.80/8.00  --min_unsat_core                        false
% 58.80/8.00  --soft_assumptions                      false
% 58.80/8.00  --soft_lemma_size                       3
% 58.80/8.00  --prop_impl_unit_size                   0
% 58.80/8.00  --prop_impl_unit                        []
% 58.80/8.00  --share_sel_clauses                     true
% 58.80/8.00  --reset_solvers                         false
% 58.80/8.00  --bc_imp_inh                            [conj_cone]
% 58.80/8.00  --conj_cone_tolerance                   3.
% 58.80/8.00  --extra_neg_conj                        none
% 58.80/8.00  --large_theory_mode                     true
% 58.80/8.00  --prolific_symb_bound                   200
% 58.80/8.00  --lt_threshold                          2000
% 58.80/8.00  --clause_weak_htbl                      true
% 58.80/8.00  --gc_record_bc_elim                     false
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing Options
% 58.80/8.00  
% 58.80/8.00  --preprocessing_flag                    true
% 58.80/8.00  --time_out_prep_mult                    0.1
% 58.80/8.00  --splitting_mode                        input
% 58.80/8.00  --splitting_grd                         true
% 58.80/8.00  --splitting_cvd                         false
% 58.80/8.00  --splitting_cvd_svl                     false
% 58.80/8.00  --splitting_nvd                         32
% 58.80/8.00  --sub_typing                            true
% 58.80/8.00  --prep_gs_sim                           true
% 58.80/8.00  --prep_unflatten                        true
% 58.80/8.00  --prep_res_sim                          true
% 58.80/8.00  --prep_upred                            true
% 58.80/8.00  --prep_sem_filter                       exhaustive
% 58.80/8.00  --prep_sem_filter_out                   false
% 58.80/8.00  --pred_elim                             true
% 58.80/8.00  --res_sim_input                         true
% 58.80/8.00  --eq_ax_congr_red                       true
% 58.80/8.00  --pure_diseq_elim                       true
% 58.80/8.00  --brand_transform                       false
% 58.80/8.00  --non_eq_to_eq                          false
% 58.80/8.00  --prep_def_merge                        true
% 58.80/8.00  --prep_def_merge_prop_impl              false
% 58.80/8.00  --prep_def_merge_mbd                    true
% 58.80/8.00  --prep_def_merge_tr_red                 false
% 58.80/8.00  --prep_def_merge_tr_cl                  false
% 58.80/8.00  --smt_preprocessing                     true
% 58.80/8.00  --smt_ac_axioms                         fast
% 58.80/8.00  --preprocessed_out                      false
% 58.80/8.00  --preprocessed_stats                    false
% 58.80/8.00  
% 58.80/8.00  ------ Abstraction refinement Options
% 58.80/8.00  
% 58.80/8.00  --abstr_ref                             []
% 58.80/8.00  --abstr_ref_prep                        false
% 58.80/8.00  --abstr_ref_until_sat                   false
% 58.80/8.00  --abstr_ref_sig_restrict                funpre
% 58.80/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 58.80/8.00  --abstr_ref_under                       []
% 58.80/8.00  
% 58.80/8.00  ------ SAT Options
% 58.80/8.00  
% 58.80/8.00  --sat_mode                              false
% 58.80/8.00  --sat_fm_restart_options                ""
% 58.80/8.00  --sat_gr_def                            false
% 58.80/8.00  --sat_epr_types                         true
% 58.80/8.00  --sat_non_cyclic_types                  false
% 58.80/8.00  --sat_finite_models                     false
% 58.80/8.00  --sat_fm_lemmas                         false
% 58.80/8.00  --sat_fm_prep                           false
% 58.80/8.00  --sat_fm_uc_incr                        true
% 58.80/8.00  --sat_out_model                         small
% 58.80/8.00  --sat_out_clauses                       false
% 58.80/8.00  
% 58.80/8.00  ------ QBF Options
% 58.80/8.00  
% 58.80/8.00  --qbf_mode                              false
% 58.80/8.00  --qbf_elim_univ                         false
% 58.80/8.00  --qbf_dom_inst                          none
% 58.80/8.00  --qbf_dom_pre_inst                      false
% 58.80/8.00  --qbf_sk_in                             false
% 58.80/8.00  --qbf_pred_elim                         true
% 58.80/8.00  --qbf_split                             512
% 58.80/8.00  
% 58.80/8.00  ------ BMC1 Options
% 58.80/8.00  
% 58.80/8.00  --bmc1_incremental                      false
% 58.80/8.00  --bmc1_axioms                           reachable_all
% 58.80/8.00  --bmc1_min_bound                        0
% 58.80/8.00  --bmc1_max_bound                        -1
% 58.80/8.00  --bmc1_max_bound_default                -1
% 58.80/8.00  --bmc1_symbol_reachability              true
% 58.80/8.00  --bmc1_property_lemmas                  false
% 58.80/8.00  --bmc1_k_induction                      false
% 58.80/8.00  --bmc1_non_equiv_states                 false
% 58.80/8.00  --bmc1_deadlock                         false
% 58.80/8.00  --bmc1_ucm                              false
% 58.80/8.00  --bmc1_add_unsat_core                   none
% 58.80/8.00  --bmc1_unsat_core_children              false
% 58.80/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 58.80/8.00  --bmc1_out_stat                         full
% 58.80/8.00  --bmc1_ground_init                      false
% 58.80/8.00  --bmc1_pre_inst_next_state              false
% 58.80/8.00  --bmc1_pre_inst_state                   false
% 58.80/8.00  --bmc1_pre_inst_reach_state             false
% 58.80/8.00  --bmc1_out_unsat_core                   false
% 58.80/8.00  --bmc1_aig_witness_out                  false
% 58.80/8.00  --bmc1_verbose                          false
% 58.80/8.00  --bmc1_dump_clauses_tptp                false
% 58.80/8.00  --bmc1_dump_unsat_core_tptp             false
% 58.80/8.00  --bmc1_dump_file                        -
% 58.80/8.00  --bmc1_ucm_expand_uc_limit              128
% 58.80/8.00  --bmc1_ucm_n_expand_iterations          6
% 58.80/8.00  --bmc1_ucm_extend_mode                  1
% 58.80/8.00  --bmc1_ucm_init_mode                    2
% 58.80/8.00  --bmc1_ucm_cone_mode                    none
% 58.80/8.00  --bmc1_ucm_reduced_relation_type        0
% 58.80/8.00  --bmc1_ucm_relax_model                  4
% 58.80/8.00  --bmc1_ucm_full_tr_after_sat            true
% 58.80/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 58.80/8.00  --bmc1_ucm_layered_model                none
% 58.80/8.00  --bmc1_ucm_max_lemma_size               10
% 58.80/8.00  
% 58.80/8.00  ------ AIG Options
% 58.80/8.00  
% 58.80/8.00  --aig_mode                              false
% 58.80/8.00  
% 58.80/8.00  ------ Instantiation Options
% 58.80/8.00  
% 58.80/8.00  --instantiation_flag                    true
% 58.80/8.00  --inst_sos_flag                         false
% 58.80/8.00  --inst_sos_phase                        true
% 58.80/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 58.80/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 58.80/8.00  --inst_lit_sel_side                     none
% 58.80/8.00  --inst_solver_per_active                1400
% 58.80/8.00  --inst_solver_calls_frac                1.
% 58.80/8.00  --inst_passive_queue_type               priority_queues
% 58.80/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 58.80/8.00  --inst_passive_queues_freq              [25;2]
% 58.80/8.00  --inst_dismatching                      true
% 58.80/8.00  --inst_eager_unprocessed_to_passive     true
% 58.80/8.00  --inst_prop_sim_given                   true
% 58.80/8.00  --inst_prop_sim_new                     false
% 58.80/8.00  --inst_subs_new                         false
% 58.80/8.00  --inst_eq_res_simp                      false
% 58.80/8.00  --inst_subs_given                       false
% 58.80/8.00  --inst_orphan_elimination               true
% 58.80/8.00  --inst_learning_loop_flag               true
% 58.80/8.00  --inst_learning_start                   3000
% 58.80/8.00  --inst_learning_factor                  2
% 58.80/8.00  --inst_start_prop_sim_after_learn       3
% 58.80/8.00  --inst_sel_renew                        solver
% 58.80/8.00  --inst_lit_activity_flag                true
% 58.80/8.00  --inst_restr_to_given                   false
% 58.80/8.00  --inst_activity_threshold               500
% 58.80/8.00  --inst_out_proof                        true
% 58.80/8.00  
% 58.80/8.00  ------ Resolution Options
% 58.80/8.00  
% 58.80/8.00  --resolution_flag                       false
% 58.80/8.00  --res_lit_sel                           adaptive
% 58.80/8.00  --res_lit_sel_side                      none
% 58.80/8.00  --res_ordering                          kbo
% 58.80/8.00  --res_to_prop_solver                    active
% 58.80/8.00  --res_prop_simpl_new                    false
% 58.80/8.00  --res_prop_simpl_given                  true
% 58.80/8.00  --res_passive_queue_type                priority_queues
% 58.80/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 58.80/8.00  --res_passive_queues_freq               [15;5]
% 58.80/8.00  --res_forward_subs                      full
% 58.80/8.00  --res_backward_subs                     full
% 58.80/8.00  --res_forward_subs_resolution           true
% 58.80/8.00  --res_backward_subs_resolution          true
% 58.80/8.00  --res_orphan_elimination                true
% 58.80/8.00  --res_time_limit                        2.
% 58.80/8.00  --res_out_proof                         true
% 58.80/8.00  
% 58.80/8.00  ------ Superposition Options
% 58.80/8.00  
% 58.80/8.00  --superposition_flag                    true
% 58.80/8.00  --sup_passive_queue_type                priority_queues
% 58.80/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 58.80/8.00  --sup_passive_queues_freq               [8;1;4]
% 58.80/8.00  --demod_completeness_check              fast
% 58.80/8.00  --demod_use_ground                      true
% 58.80/8.00  --sup_to_prop_solver                    passive
% 58.80/8.00  --sup_prop_simpl_new                    true
% 58.80/8.00  --sup_prop_simpl_given                  true
% 58.80/8.00  --sup_fun_splitting                     false
% 58.80/8.00  --sup_smt_interval                      50000
% 58.80/8.00  
% 58.80/8.00  ------ Superposition Simplification Setup
% 58.80/8.00  
% 58.80/8.00  --sup_indices_passive                   []
% 58.80/8.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 58.80/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 58.80/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_full_bw                           [BwDemod]
% 58.80/8.00  --sup_immed_triv                        [TrivRules]
% 58.80/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 58.80/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_immed_bw_main                     []
% 58.80/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 58.80/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 58.80/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 58.80/8.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 58.80/8.00  
% 58.80/8.00  ------ Combination Options
% 58.80/8.00  
% 58.80/8.00  --comb_res_mult                         3
% 58.80/8.00  --comb_sup_mult                         2
% 58.80/8.00  --comb_inst_mult                        10
% 58.80/8.00  
% 58.80/8.00  ------ Debug Options
% 58.80/8.00  
% 58.80/8.00  --dbg_backtrace                         false
% 58.80/8.00  --dbg_dump_prop_clauses                 false
% 58.80/8.00  --dbg_dump_prop_clauses_file            -
% 58.80/8.00  --dbg_out_stat                          false
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  ------ Proving...
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  % SZS status Theorem for theBenchmark.p
% 58.80/8.00  
% 58.80/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 58.80/8.00  
% 58.80/8.00  fof(f3,axiom,(
% 58.80/8.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f24,plain,(
% 58.80/8.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 58.80/8.00    inference(nnf_transformation,[],[f3])).
% 58.80/8.00  
% 58.80/8.00  fof(f25,plain,(
% 58.80/8.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 58.80/8.00    inference(flattening,[],[f24])).
% 58.80/8.00  
% 58.80/8.00  fof(f26,plain,(
% 58.80/8.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 58.80/8.00    inference(rectify,[],[f25])).
% 58.80/8.00  
% 58.80/8.00  fof(f27,plain,(
% 58.80/8.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f28,plain,(
% 58.80/8.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 58.80/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 58.80/8.00  
% 58.80/8.00  fof(f48,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f28])).
% 58.80/8.00  
% 58.80/8.00  fof(f4,axiom,(
% 58.80/8.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f49,plain,(
% 58.80/8.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 58.80/8.00    inference(cnf_transformation,[],[f4])).
% 58.80/8.00  
% 58.80/8.00  fof(f65,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(definition_unfolding,[],[f48,f49])).
% 58.80/8.00  
% 58.80/8.00  fof(f6,axiom,(
% 58.80/8.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f12,plain,(
% 58.80/8.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 58.80/8.00    inference(ennf_transformation,[],[f6])).
% 58.80/8.00  
% 58.80/8.00  fof(f33,plain,(
% 58.80/8.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 58.80/8.00    inference(nnf_transformation,[],[f12])).
% 58.80/8.00  
% 58.80/8.00  fof(f55,plain,(
% 58.80/8.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f33])).
% 58.80/8.00  
% 58.80/8.00  fof(f1,axiom,(
% 58.80/8.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f16,plain,(
% 58.80/8.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 58.80/8.00    inference(nnf_transformation,[],[f1])).
% 58.80/8.00  
% 58.80/8.00  fof(f17,plain,(
% 58.80/8.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 58.80/8.00    inference(rectify,[],[f16])).
% 58.80/8.00  
% 58.80/8.00  fof(f18,plain,(
% 58.80/8.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f19,plain,(
% 58.80/8.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 58.80/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 58.80/8.00  
% 58.80/8.00  fof(f38,plain,(
% 58.80/8.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f19])).
% 58.80/8.00  
% 58.80/8.00  fof(f9,conjecture,(
% 58.80/8.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f10,negated_conjecture,(
% 58.80/8.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 58.80/8.00    inference(negated_conjecture,[],[f9])).
% 58.80/8.00  
% 58.80/8.00  fof(f14,plain,(
% 58.80/8.00    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 58.80/8.00    inference(ennf_transformation,[],[f10])).
% 58.80/8.00  
% 58.80/8.00  fof(f15,plain,(
% 58.80/8.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 58.80/8.00    inference(flattening,[],[f14])).
% 58.80/8.00  
% 58.80/8.00  fof(f34,plain,(
% 58.80/8.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 58.80/8.00    inference(nnf_transformation,[],[f15])).
% 58.80/8.00  
% 58.80/8.00  fof(f36,plain,(
% 58.80/8.00    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK6) != X1 & ! [X3] : (((~r2_hidden(X3,sK6) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,sK6) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK6,k1_zfmisc_1(X0)))) )),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f35,plain,(
% 58.80/8.00    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK4,X2) != sK5 & ! [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,sK5)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK5))) | ~m1_subset_1(X3,sK4)) & m1_subset_1(X2,k1_zfmisc_1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f37,plain,(
% 58.80/8.00    (k3_subset_1(sK4,sK6) != sK5 & ! [X3] : (((~r2_hidden(X3,sK6) | ~r2_hidden(X3,sK5)) & (r2_hidden(X3,sK6) | r2_hidden(X3,sK5))) | ~m1_subset_1(X3,sK4)) & m1_subset_1(sK6,k1_zfmisc_1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 58.80/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f34,f36,f35])).
% 58.80/8.00  
% 58.80/8.00  fof(f63,plain,(
% 58.80/8.00    ( ! [X3] : (~r2_hidden(X3,sK6) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,sK4)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f37])).
% 58.80/8.00  
% 58.80/8.00  fof(f46,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f28])).
% 58.80/8.00  
% 58.80/8.00  fof(f67,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(definition_unfolding,[],[f46,f49])).
% 58.80/8.00  
% 58.80/8.00  fof(f2,axiom,(
% 58.80/8.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f11,plain,(
% 58.80/8.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 58.80/8.00    inference(ennf_transformation,[],[f2])).
% 58.80/8.00  
% 58.80/8.00  fof(f20,plain,(
% 58.80/8.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 58.80/8.00    inference(nnf_transformation,[],[f11])).
% 58.80/8.00  
% 58.80/8.00  fof(f21,plain,(
% 58.80/8.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 58.80/8.00    inference(rectify,[],[f20])).
% 58.80/8.00  
% 58.80/8.00  fof(f22,plain,(
% 58.80/8.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f23,plain,(
% 58.80/8.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 58.80/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 58.80/8.00  
% 58.80/8.00  fof(f40,plain,(
% 58.80/8.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f23])).
% 58.80/8.00  
% 58.80/8.00  fof(f62,plain,(
% 58.80/8.00    ( ! [X3] : (r2_hidden(X3,sK6) | r2_hidden(X3,sK5) | ~m1_subset_1(X3,sK4)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f37])).
% 58.80/8.00  
% 58.80/8.00  fof(f47,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f28])).
% 58.80/8.00  
% 58.80/8.00  fof(f66,plain,(
% 58.80/8.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 58.80/8.00    inference(definition_unfolding,[],[f47,f49])).
% 58.80/8.00  
% 58.80/8.00  fof(f5,axiom,(
% 58.80/8.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f29,plain,(
% 58.80/8.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 58.80/8.00    inference(nnf_transformation,[],[f5])).
% 58.80/8.00  
% 58.80/8.00  fof(f30,plain,(
% 58.80/8.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 58.80/8.00    inference(rectify,[],[f29])).
% 58.80/8.00  
% 58.80/8.00  fof(f31,plain,(
% 58.80/8.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 58.80/8.00    introduced(choice_axiom,[])).
% 58.80/8.00  
% 58.80/8.00  fof(f32,plain,(
% 58.80/8.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 58.80/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 58.80/8.00  
% 58.80/8.00  fof(f50,plain,(
% 58.80/8.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 58.80/8.00    inference(cnf_transformation,[],[f32])).
% 58.80/8.00  
% 58.80/8.00  fof(f76,plain,(
% 58.80/8.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 58.80/8.00    inference(equality_resolution,[],[f50])).
% 58.80/8.00  
% 58.80/8.00  fof(f7,axiom,(
% 58.80/8.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f13,plain,(
% 58.80/8.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 58.80/8.00    inference(ennf_transformation,[],[f7])).
% 58.80/8.00  
% 58.80/8.00  fof(f58,plain,(
% 58.80/8.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 58.80/8.00    inference(cnf_transformation,[],[f13])).
% 58.80/8.00  
% 58.80/8.00  fof(f71,plain,(
% 58.80/8.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 58.80/8.00    inference(definition_unfolding,[],[f58,f49])).
% 58.80/8.00  
% 58.80/8.00  fof(f61,plain,(
% 58.80/8.00    m1_subset_1(sK6,k1_zfmisc_1(sK4))),
% 58.80/8.00    inference(cnf_transformation,[],[f37])).
% 58.80/8.00  
% 58.80/8.00  fof(f54,plain,(
% 58.80/8.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 58.80/8.00    inference(cnf_transformation,[],[f33])).
% 58.80/8.00  
% 58.80/8.00  fof(f60,plain,(
% 58.80/8.00    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 58.80/8.00    inference(cnf_transformation,[],[f37])).
% 58.80/8.00  
% 58.80/8.00  fof(f8,axiom,(
% 58.80/8.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 58.80/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.80/8.00  
% 58.80/8.00  fof(f59,plain,(
% 58.80/8.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 58.80/8.00    inference(cnf_transformation,[],[f8])).
% 58.80/8.00  
% 58.80/8.00  fof(f64,plain,(
% 58.80/8.00    k3_subset_1(sK4,sK6) != sK5),
% 58.80/8.00    inference(cnf_transformation,[],[f37])).
% 58.80/8.00  
% 58.80/8.00  cnf(c_742,plain,( X0 = X0 ),theory(equality) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_264039,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) = k3_subset_1(sK4,sK6) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_742]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_743,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_223149,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != X0
% 58.80/8.00      | k3_subset_1(sK4,sK6) = k5_xboole_0(X1,k3_xboole_0(X1,sK6))
% 58.80/8.00      | k5_xboole_0(X1,k3_xboole_0(X1,sK6)) != X0 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_743]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_264038,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != k3_subset_1(sK4,sK6)
% 58.80/8.00      | k3_subset_1(sK4,sK6) = k5_xboole_0(X0,k3_xboole_0(X0,sK6))
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) != k3_subset_1(sK4,sK6) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_223149]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_264040,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != k3_subset_1(sK4,sK6)
% 58.80/8.00      | k3_subset_1(sK4,sK6) = k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
% 58.80/8.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) != k3_subset_1(sK4,sK6) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_264038]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_193709,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != X0
% 58.80/8.00      | k3_subset_1(sK4,sK6) = sK5
% 58.80/8.00      | sK5 != X0 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_743]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_219667,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != k5_xboole_0(X0,k3_xboole_0(X0,sK6))
% 58.80/8.00      | k3_subset_1(sK4,sK6) = sK5
% 58.80/8.00      | sK5 != k5_xboole_0(X0,k3_xboole_0(X0,sK6)) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_193709]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_219668,plain,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
% 58.80/8.00      | k3_subset_1(sK4,sK6) = sK5
% 58.80/8.00      | sK5 != k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_219667]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 58.80/8.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 58.80/8.00      inference(cnf_transformation,[],[f65]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_14116,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,sK6,X1),X0)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,X1),X1)
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,X1),sK6)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = X1 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_5]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_35433,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,sK6,sK5),X0)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_14116]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_35434,plain,
% 58.80/8.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),X0) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6) = iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_35433]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_35436,plain,
% 58.80/8.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK6) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_35434]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_17,plain,
% 58.80/8.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 58.80/8.00      inference(cnf_transformation,[],[f55]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1,plain,
% 58.80/8.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 58.80/8.00      inference(cnf_transformation,[],[f38]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_145,plain,
% 58.80/8.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 58.80/8.00      inference(global_propositional_subsumption,
% 58.80/8.00                [status(thm)],
% 58.80/8.00                [c_17,c_1]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_146,plain,
% 58.80/8.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 58.80/8.00      inference(renaming,[status(thm)],[c_145]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_22,negated_conjecture,
% 58.80/8.00      ( ~ m1_subset_1(X0,sK4)
% 58.80/8.00      | ~ r2_hidden(X0,sK5)
% 58.80/8.00      | ~ r2_hidden(X0,sK6) ),
% 58.80/8.00      inference(cnf_transformation,[],[f63]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_539,plain,
% 58.80/8.00      ( ~ r2_hidden(X0,X1)
% 58.80/8.00      | ~ r2_hidden(X2,sK5)
% 58.80/8.00      | ~ r2_hidden(X2,sK6)
% 58.80/8.00      | X2 != X0
% 58.80/8.00      | sK4 != X1 ),
% 58.80/8.00      inference(resolution_lifted,[status(thm)],[c_146,c_22]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_540,plain,
% 58.80/8.00      ( ~ r2_hidden(X0,sK5) | ~ r2_hidden(X0,sK6) | ~ r2_hidden(X0,sK4) ),
% 58.80/8.00      inference(unflattening,[status(thm)],[c_539]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_2775,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,X1,sK5),sK5)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,X1,sK5),sK6)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,X1,sK5),sK4) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_540]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_19273,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK6)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK4) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_2775]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_19274,plain,
% 58.80/8.00      ( r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK4) != iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_19273]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_19276,plain,
% 58.80/8.00      ( r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK6) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_19274]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1709,plain,
% 58.80/8.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_743]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1820,plain,
% 58.80/8.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_1709]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_15396,plain,
% 58.80/8.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) != sK5
% 58.80/8.00      | sK5 = k5_xboole_0(sK4,k3_xboole_0(sK4,sK6))
% 58.80/8.00      | sK5 != sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_1820]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_7,plain,
% 58.80/8.00      ( r2_hidden(sK2(X0,X1,X2),X0)
% 58.80/8.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 58.80/8.00      inference(cnf_transformation,[],[f67]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_8362,plain,
% 58.80/8.00      ( r2_hidden(sK2(sK4,sK6,sK5),sK5)
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4)
% 58.80/8.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_7]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_8365,plain,
% 58.80/8.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4) = iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_8362]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_4,plain,
% 58.80/8.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 58.80/8.00      inference(cnf_transformation,[],[f40]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1629,plain,
% 58.80/8.00      ( ~ r1_tarski(sK5,X0) | r2_hidden(X1,X0) | ~ r2_hidden(X1,sK5) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_8328,plain,
% 58.80/8.00      ( ~ r1_tarski(sK5,sK4)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK5)
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK4) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_1629]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_8329,plain,
% 58.80/8.00      ( r1_tarski(sK5,sK4) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK4) = iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_8328]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_8331,plain,
% 58.80/8.00      ( r1_tarski(sK5,sK4) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK5) != iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4) = iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_8329]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_23,negated_conjecture,
% 58.80/8.00      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK5) | r2_hidden(X0,sK6) ),
% 58.80/8.00      inference(cnf_transformation,[],[f62]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_524,plain,
% 58.80/8.00      ( ~ r2_hidden(X0,X1)
% 58.80/8.00      | r2_hidden(X2,sK5)
% 58.80/8.00      | r2_hidden(X2,sK6)
% 58.80/8.00      | X2 != X0
% 58.80/8.00      | sK4 != X1 ),
% 58.80/8.00      inference(resolution_lifted,[status(thm)],[c_146,c_23]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_525,plain,
% 58.80/8.00      ( r2_hidden(X0,sK5) | r2_hidden(X0,sK6) | ~ r2_hidden(X0,sK4) ),
% 58.80/8.00      inference(unflattening,[status(thm)],[c_524]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5259,plain,
% 58.80/8.00      ( r2_hidden(sK2(X0,sK6,sK5),sK5)
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK4) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_525]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5264,plain,
% 58.80/8.00      ( r2_hidden(sK2(X0,sK6,sK5),sK5) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK4) != iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_5259]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5266,plain,
% 58.80/8.00      ( r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK6) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK4) != iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_5264]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_6,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
% 58.80/8.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 58.80/8.00      inference(cnf_transformation,[],[f66]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_2773,plain,
% 58.80/8.00      ( ~ r2_hidden(sK2(X0,X1,sK5),X1)
% 58.80/8.00      | r2_hidden(sK2(X0,X1,sK5),sK5)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5253,plain,
% 58.80/8.00      ( r2_hidden(sK2(X0,sK6,sK5),sK5)
% 58.80/8.00      | ~ r2_hidden(sK2(X0,sK6,sK5),sK6)
% 58.80/8.00      | k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_2773]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5260,plain,
% 58.80/8.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = sK5
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK5) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(X0,sK6,sK5),sK6) != iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_5253]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_5262,plain,
% 58.80/8.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = sK5
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK5) = iProver_top
% 58.80/8.00      | r2_hidden(sK2(sK4,sK6,sK5),sK6) != iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_5260]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_14,plain,
% 58.80/8.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 58.80/8.00      inference(cnf_transformation,[],[f76]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1907,plain,
% 58.80/8.00      ( r1_tarski(sK5,sK4) | ~ r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_14]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1908,plain,
% 58.80/8.00      ( r1_tarski(sK5,sK4) = iProver_top
% 58.80/8.00      | r2_hidden(sK5,k1_zfmisc_1(sK4)) != iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_1907]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_1821,plain,
% 58.80/8.00      ( sK5 = sK5 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_742]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_759,plain,
% 58.80/8.00      ( sK4 = sK4 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_742]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_749,plain,
% 58.80/8.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 58.80/8.00      theory(equality) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_756,plain,
% 58.80/8.00      ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) | sK4 != sK4 ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_749]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_19,plain,
% 58.80/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 58.80/8.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 58.80/8.00      inference(cnf_transformation,[],[f71]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_24,negated_conjecture,
% 58.80/8.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
% 58.80/8.00      inference(cnf_transformation,[],[f61]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_626,plain,
% 58.80/8.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 58.80/8.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 58.80/8.00      | sK6 != X1 ),
% 58.80/8.00      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_627,plain,
% 58.80/8.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
% 58.80/8.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 58.80/8.00      inference(unflattening,[status(thm)],[c_626]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_628,plain,
% 58.80/8.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = k3_subset_1(sK4,sK6)
% 58.80/8.00      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_627]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_18,plain,
% 58.80/8.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 58.80/8.00      inference(cnf_transformation,[],[f54]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_25,negated_conjecture,
% 58.80/8.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 58.80/8.00      inference(cnf_transformation,[],[f60]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_608,plain,
% 58.80/8.00      ( r2_hidden(X0,X1)
% 58.80/8.00      | v1_xboole_0(X1)
% 58.80/8.00      | k1_zfmisc_1(sK4) != X1
% 58.80/8.00      | sK5 != X0 ),
% 58.80/8.00      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_609,plain,
% 58.80/8.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 58.80/8.00      inference(unflattening,[status(thm)],[c_608]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_610,plain,
% 58.80/8.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 58.80/8.00      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_20,plain,
% 58.80/8.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 58.80/8.00      inference(cnf_transformation,[],[f59]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_34,plain,
% 58.80/8.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 58.80/8.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_36,plain,
% 58.80/8.00      ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 58.80/8.00      inference(instantiation,[status(thm)],[c_34]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(c_21,negated_conjecture,
% 58.80/8.00      ( k3_subset_1(sK4,sK6) != sK5 ),
% 58.80/8.00      inference(cnf_transformation,[],[f64]) ).
% 58.80/8.00  
% 58.80/8.00  cnf(contradiction,plain,
% 58.80/8.00      ( $false ),
% 58.80/8.00      inference(minisat,
% 58.80/8.00                [status(thm)],
% 58.80/8.00                [c_264039,c_264040,c_219668,c_35436,c_19276,c_15396,
% 58.80/8.00                 c_8365,c_8331,c_5266,c_5262,c_1908,c_1821,c_759,c_756,
% 58.80/8.00                 c_628,c_610,c_36,c_21]) ).
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 58.80/8.00  
% 58.80/8.00  ------                               Statistics
% 58.80/8.00  
% 58.80/8.00  ------ General
% 58.80/8.00  
% 58.80/8.00  abstr_ref_over_cycles:                  0
% 58.80/8.00  abstr_ref_under_cycles:                 0
% 58.80/8.00  gc_basic_clause_elim:                   0
% 58.80/8.00  forced_gc_time:                         0
% 58.80/8.00  parsing_time:                           0.009
% 58.80/8.00  unif_index_cands_time:                  0.
% 58.80/8.00  unif_index_add_time:                    0.
% 58.80/8.00  orderings_time:                         0.
% 58.80/8.00  out_proof_time:                         0.105
% 58.80/8.00  total_time:                             7.122
% 58.80/8.00  num_of_symbols:                         46
% 58.80/8.00  num_of_terms:                           235085
% 58.80/8.00  
% 58.80/8.00  ------ Preprocessing
% 58.80/8.00  
% 58.80/8.00  num_of_splits:                          0
% 58.80/8.00  num_of_split_atoms:                     0
% 58.80/8.00  num_of_reused_defs:                     0
% 58.80/8.00  num_eq_ax_congr_red:                    23
% 58.80/8.00  num_of_sem_filtered_clauses:            1
% 58.80/8.00  num_of_subtypes:                        0
% 58.80/8.00  monotx_restored_types:                  0
% 58.80/8.00  sat_num_of_epr_types:                   0
% 58.80/8.00  sat_num_of_non_cyclic_types:            0
% 58.80/8.00  sat_guarded_non_collapsed_types:        0
% 58.80/8.00  num_pure_diseq_elim:                    0
% 58.80/8.00  simp_replaced_by:                       0
% 58.80/8.00  res_preprocessed:                       105
% 58.80/8.00  prep_upred:                             0
% 58.80/8.00  prep_unflattend:                        36
% 58.80/8.00  smt_new_axioms:                         0
% 58.80/8.00  pred_elim_cands:                        4
% 58.80/8.00  pred_elim:                              1
% 58.80/8.00  pred_elim_cl:                           -4
% 58.80/8.00  pred_elim_cycles:                       3
% 58.80/8.00  merged_defs:                            6
% 58.80/8.00  merged_defs_ncl:                        0
% 58.80/8.00  bin_hyper_res:                          7
% 58.80/8.00  prep_cycles:                            3
% 58.80/8.00  pred_elim_time:                         0.005
% 58.80/8.00  splitting_time:                         0.
% 58.80/8.00  sem_filter_time:                        0.
% 58.80/8.00  monotx_time:                            0.001
% 58.80/8.00  subtype_inf_time:                       0.
% 58.80/8.00  
% 58.80/8.00  ------ Problem properties
% 58.80/8.00  
% 58.80/8.00  clauses:                                30
% 58.80/8.00  conjectures:                            1
% 58.80/8.00  epr:                                    6
% 58.80/8.00  horn:                                   19
% 58.80/8.00  ground:                                 7
% 58.80/8.00  unary:                                  4
% 58.80/8.00  binary:                                 11
% 58.80/8.00  lits:                                   74
% 58.80/8.00  lits_eq:                                15
% 58.80/8.00  fd_pure:                                0
% 58.80/8.00  fd_pseudo:                              0
% 58.80/8.00  fd_cond:                                0
% 58.80/8.00  fd_pseudo_cond:                         5
% 58.80/8.00  ac_symbols:                             0
% 58.80/8.00  
% 58.80/8.00  ------ Propositional Solver
% 58.80/8.00  
% 58.80/8.00  prop_solver_calls:                      72
% 58.80/8.00  prop_fast_solver_calls:                 3364
% 58.80/8.00  smt_solver_calls:                       0
% 58.80/8.00  smt_fast_solver_calls:                  0
% 58.80/8.00  prop_num_of_clauses:                    71070
% 58.80/8.00  prop_preprocess_simplified:             131725
% 58.80/8.00  prop_fo_subsumed:                       166
% 58.80/8.00  prop_solver_time:                       0.
% 58.80/8.00  smt_solver_time:                        0.
% 58.80/8.00  smt_fast_solver_time:                   0.
% 58.80/8.00  prop_fast_solver_time:                  0.
% 58.80/8.00  prop_unsat_core_time:                   0.096
% 58.80/8.00  
% 58.80/8.00  ------ QBF
% 58.80/8.00  
% 58.80/8.00  qbf_q_res:                              0
% 58.80/8.00  qbf_num_tautologies:                    0
% 58.80/8.00  qbf_prep_cycles:                        0
% 58.80/8.00  
% 58.80/8.00  ------ BMC1
% 58.80/8.00  
% 58.80/8.00  bmc1_current_bound:                     -1
% 58.80/8.00  bmc1_last_solved_bound:                 -1
% 58.80/8.00  bmc1_unsat_core_size:                   -1
% 58.80/8.00  bmc1_unsat_core_parents_size:           -1
% 58.80/8.00  bmc1_merge_next_fun:                    0
% 58.80/8.00  bmc1_unsat_core_clauses_time:           0.
% 58.80/8.00  
% 58.80/8.00  ------ Instantiation
% 58.80/8.00  
% 58.80/8.00  inst_num_of_clauses:                    3480
% 58.80/8.00  inst_num_in_passive:                    1910
% 58.80/8.00  inst_num_in_active:                     3242
% 58.80/8.00  inst_num_in_unprocessed:                522
% 58.80/8.00  inst_num_of_loops:                      4157
% 58.80/8.00  inst_num_of_learning_restarts:          1
% 58.80/8.00  inst_num_moves_active_passive:          912
% 58.80/8.00  inst_lit_activity:                      0
% 58.80/8.00  inst_lit_activity_moves:                2
% 58.80/8.00  inst_num_tautologies:                   0
% 58.80/8.00  inst_num_prop_implied:                  0
% 58.80/8.00  inst_num_existing_simplified:           0
% 58.80/8.00  inst_num_eq_res_simplified:             0
% 58.80/8.00  inst_num_child_elim:                    0
% 58.80/8.00  inst_num_of_dismatching_blockings:      38796
% 58.80/8.00  inst_num_of_non_proper_insts:           17707
% 58.80/8.00  inst_num_of_duplicates:                 0
% 58.80/8.00  inst_inst_num_from_inst_to_res:         0
% 58.80/8.00  inst_dismatching_checking_time:         0.
% 58.80/8.00  
% 58.80/8.00  ------ Resolution
% 58.80/8.00  
% 58.80/8.00  res_num_of_clauses:                     39
% 58.80/8.00  res_num_in_passive:                     39
% 58.80/8.00  res_num_in_active:                      0
% 58.80/8.00  res_num_of_loops:                       108
% 58.80/8.00  res_forward_subset_subsumed:            266
% 58.80/8.00  res_backward_subset_subsumed:           2
% 58.80/8.00  res_forward_subsumed:                   3
% 58.80/8.00  res_backward_subsumed:                  0
% 58.80/8.00  res_forward_subsumption_resolution:     0
% 58.80/8.00  res_backward_subsumption_resolution:    0
% 58.80/8.00  res_clause_to_clause_subsumption:       75293
% 58.80/8.00  res_orphan_elimination:                 0
% 58.80/8.00  res_tautology_del:                      5913
% 58.80/8.00  res_num_eq_res_simplified:              0
% 58.80/8.00  res_num_sel_changes:                    0
% 58.80/8.00  res_moves_from_active_to_pass:          0
% 58.80/8.00  
% 58.80/8.00  ------ Superposition
% 58.80/8.00  
% 58.80/8.00  sup_time_total:                         0.
% 58.80/8.00  sup_time_generating:                    0.
% 58.80/8.00  sup_time_sim_full:                      0.
% 58.80/8.00  sup_time_sim_immed:                     0.
% 58.80/8.00  
% 58.80/8.00  sup_num_of_clauses:                     7656
% 58.80/8.00  sup_num_in_active:                      784
% 58.80/8.00  sup_num_in_passive:                     6872
% 58.80/8.00  sup_num_of_loops:                       830
% 58.80/8.00  sup_fw_superposition:                   4902
% 58.80/8.00  sup_bw_superposition:                   7113
% 58.80/8.00  sup_immediate_simplified:               3521
% 58.80/8.00  sup_given_eliminated:                   4
% 58.80/8.00  comparisons_done:                       0
% 58.80/8.00  comparisons_avoided:                    41
% 58.80/8.00  
% 58.80/8.00  ------ Simplifications
% 58.80/8.00  
% 58.80/8.00  
% 58.80/8.00  sim_fw_subset_subsumed:                 1061
% 58.80/8.00  sim_bw_subset_subsumed:                 125
% 58.80/8.00  sim_fw_subsumed:                        1392
% 58.80/8.00  sim_bw_subsumed:                        144
% 58.80/8.00  sim_fw_subsumption_res:                 70
% 58.80/8.00  sim_bw_subsumption_res:                 30
% 58.80/8.00  sim_tautology_del:                      292
% 58.80/8.00  sim_eq_tautology_del:                   26
% 58.80/8.00  sim_eq_res_simp:                        44
% 58.80/8.00  sim_fw_demodulated:                     438
% 58.80/8.00  sim_bw_demodulated:                     106
% 58.80/8.00  sim_light_normalised:                   584
% 58.80/8.00  sim_joinable_taut:                      0
% 58.80/8.00  sim_joinable_simp:                      0
% 58.80/8.00  sim_ac_normalised:                      0
% 58.80/8.00  sim_smt_subsumption:                    0
% 58.80/8.00  
%------------------------------------------------------------------------------
