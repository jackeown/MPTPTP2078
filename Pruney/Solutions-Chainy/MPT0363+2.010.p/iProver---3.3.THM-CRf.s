%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:37 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 416 expanded)
%              Number of clauses        :   58 ( 118 expanded)
%              Number of leaves         :   17 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  452 (1757 expanded)
%              Number of equality atoms :  109 ( 255 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,k3_subset_1(X0,sK6))
          | ~ r1_xboole_0(X1,sK6) )
        & ( r1_tarski(X1,k3_subset_1(X0,sK6))
          | r1_xboole_0(X1,sK6) )
        & m1_subset_1(sK6,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK5,k3_subset_1(sK4,X2))
            | ~ r1_xboole_0(sK5,X2) )
          & ( r1_tarski(sK5,k3_subset_1(sK4,X2))
            | r1_xboole_0(sK5,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK6))
      | ~ r1_xboole_0(sK5,sK6) )
    & ( r1_tarski(sK5,k3_subset_1(sK4,sK6))
      | r1_xboole_0(sK5,sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f41,f40])).

fof(f70,plain,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK6))
    | r1_xboole_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f14])).

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
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f56])).

fof(f69,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
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

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f71,plain,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK6))
    | ~ r1_xboole_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1201,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(sK5,sK6)
    | r1_tarski(sK5,k3_subset_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1194,plain,
    ( r1_xboole_0(sK5,sK6) = iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1212,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1211,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2405,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1211])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_420,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_421,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1301,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = k3_subset_1(sK4,sK6) ),
    inference(equality_resolution,[status(thm)],[c_421])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1205,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2151,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK6)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1205])).

cnf(c_11385,plain,
    ( r2_hidden(sK0(X0,X1),sK4) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_subset_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_2151])).

cnf(c_12679,plain,
    ( r1_xboole_0(sK5,sK6) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK4) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_11385])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_407,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_408,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_414,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_408,c_23])).

cnf(c_1192,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1196,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1664,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1196])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1200,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3395,plain,
    ( r1_xboole_0(X0,sK6) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK4,sK6)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1200])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(sK5,sK6)
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1195,plain,
    ( r1_xboole_0(sK5,sK6) != iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3583,plain,
    ( r1_xboole_0(sK5,sK6) != iProver_top
    | r1_tarski(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_1195])).

cnf(c_14381,plain,
    ( r2_hidden(sK0(sK5,X0),sK4) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12679,c_1664,c_3583])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1207,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3378,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1207])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1213,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3957,plain,
    ( r2_hidden(sK0(X0,k3_subset_1(sK4,sK6)),sK6) = iProver_top
    | r2_hidden(sK0(X0,k3_subset_1(sK4,sK6)),sK4) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3378,c_1213])).

cnf(c_14387,plain,
    ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK6)),sK6) = iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14381,c_3957])).

cnf(c_30,plain,
    ( r1_xboole_0(sK5,sK6) = iProver_top
    | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14662,plain,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14387,c_30,c_1664,c_3583])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1202,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2406,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1211])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1206,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2384,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK6)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1206])).

cnf(c_14601,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),sK6) != iProver_top
    | r1_tarski(X1,k3_subset_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2384])).

cnf(c_15478,plain,
    ( r1_xboole_0(X0,sK5) = iProver_top
    | r2_hidden(sK2(X0,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_14662,c_14601])).

cnf(c_15525,plain,
    ( r1_xboole_0(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_15478])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1288,plain,
    ( ~ r1_xboole_0(sK6,sK5)
    | r1_xboole_0(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1289,plain,
    ( r1_xboole_0(sK6,sK5) != iProver_top
    | r1_xboole_0(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15525,c_3583,c_1664,c_1289])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.99  
% 3.85/0.99  ------  iProver source info
% 3.85/0.99  
% 3.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.99  git: non_committed_changes: false
% 3.85/0.99  git: last_make_outside_of_git: false
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options
% 3.85/0.99  
% 3.85/0.99  --out_options                           all
% 3.85/0.99  --tptp_safe_out                         true
% 3.85/0.99  --problem_path                          ""
% 3.85/0.99  --include_path                          ""
% 3.85/0.99  --clausifier                            res/vclausify_rel
% 3.85/0.99  --clausifier_options                    ""
% 3.85/0.99  --stdin                                 false
% 3.85/0.99  --stats_out                             all
% 3.85/0.99  
% 3.85/0.99  ------ General Options
% 3.85/0.99  
% 3.85/0.99  --fof                                   false
% 3.85/0.99  --time_out_real                         305.
% 3.85/0.99  --time_out_virtual                      -1.
% 3.85/0.99  --symbol_type_check                     false
% 3.85/0.99  --clausify_out                          false
% 3.85/0.99  --sig_cnt_out                           false
% 3.85/0.99  --trig_cnt_out                          false
% 3.85/0.99  --trig_cnt_out_tolerance                1.
% 3.85/0.99  --trig_cnt_out_sk_spl                   false
% 3.85/0.99  --abstr_cl_out                          false
% 3.85/0.99  
% 3.85/0.99  ------ Global Options
% 3.85/0.99  
% 3.85/0.99  --schedule                              default
% 3.85/0.99  --add_important_lit                     false
% 3.85/0.99  --prop_solver_per_cl                    1000
% 3.85/0.99  --min_unsat_core                        false
% 3.85/0.99  --soft_assumptions                      false
% 3.85/0.99  --soft_lemma_size                       3
% 3.85/0.99  --prop_impl_unit_size                   0
% 3.85/0.99  --prop_impl_unit                        []
% 3.85/0.99  --share_sel_clauses                     true
% 3.85/0.99  --reset_solvers                         false
% 3.85/0.99  --bc_imp_inh                            [conj_cone]
% 3.85/0.99  --conj_cone_tolerance                   3.
% 3.85/0.99  --extra_neg_conj                        none
% 3.85/0.99  --large_theory_mode                     true
% 3.85/0.99  --prolific_symb_bound                   200
% 3.85/0.99  --lt_threshold                          2000
% 3.85/0.99  --clause_weak_htbl                      true
% 3.85/0.99  --gc_record_bc_elim                     false
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing Options
% 3.85/0.99  
% 3.85/0.99  --preprocessing_flag                    true
% 3.85/0.99  --time_out_prep_mult                    0.1
% 3.85/0.99  --splitting_mode                        input
% 3.85/0.99  --splitting_grd                         true
% 3.85/0.99  --splitting_cvd                         false
% 3.85/0.99  --splitting_cvd_svl                     false
% 3.85/0.99  --splitting_nvd                         32
% 3.85/0.99  --sub_typing                            true
% 3.85/0.99  --prep_gs_sim                           true
% 3.85/0.99  --prep_unflatten                        true
% 3.85/0.99  --prep_res_sim                          true
% 3.85/0.99  --prep_upred                            true
% 3.85/0.99  --prep_sem_filter                       exhaustive
% 3.85/0.99  --prep_sem_filter_out                   false
% 3.85/0.99  --pred_elim                             true
% 3.85/0.99  --res_sim_input                         true
% 3.85/0.99  --eq_ax_congr_red                       true
% 3.85/0.99  --pure_diseq_elim                       true
% 3.85/0.99  --brand_transform                       false
% 3.85/0.99  --non_eq_to_eq                          false
% 3.85/0.99  --prep_def_merge                        true
% 3.85/0.99  --prep_def_merge_prop_impl              false
% 3.85/0.99  --prep_def_merge_mbd                    true
% 3.85/0.99  --prep_def_merge_tr_red                 false
% 3.85/0.99  --prep_def_merge_tr_cl                  false
% 3.85/0.99  --smt_preprocessing                     true
% 3.85/0.99  --smt_ac_axioms                         fast
% 3.85/0.99  --preprocessed_out                      false
% 3.85/0.99  --preprocessed_stats                    false
% 3.85/0.99  
% 3.85/0.99  ------ Abstraction refinement Options
% 3.85/0.99  
% 3.85/0.99  --abstr_ref                             []
% 3.85/0.99  --abstr_ref_prep                        false
% 3.85/0.99  --abstr_ref_until_sat                   false
% 3.85/0.99  --abstr_ref_sig_restrict                funpre
% 3.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.99  --abstr_ref_under                       []
% 3.85/0.99  
% 3.85/0.99  ------ SAT Options
% 3.85/0.99  
% 3.85/0.99  --sat_mode                              false
% 3.85/0.99  --sat_fm_restart_options                ""
% 3.85/0.99  --sat_gr_def                            false
% 3.85/0.99  --sat_epr_types                         true
% 3.85/0.99  --sat_non_cyclic_types                  false
% 3.85/0.99  --sat_finite_models                     false
% 3.85/0.99  --sat_fm_lemmas                         false
% 3.85/0.99  --sat_fm_prep                           false
% 3.85/0.99  --sat_fm_uc_incr                        true
% 3.85/0.99  --sat_out_model                         small
% 3.85/0.99  --sat_out_clauses                       false
% 3.85/0.99  
% 3.85/0.99  ------ QBF Options
% 3.85/0.99  
% 3.85/0.99  --qbf_mode                              false
% 3.85/0.99  --qbf_elim_univ                         false
% 3.85/0.99  --qbf_dom_inst                          none
% 3.85/0.99  --qbf_dom_pre_inst                      false
% 3.85/0.99  --qbf_sk_in                             false
% 3.85/0.99  --qbf_pred_elim                         true
% 3.85/0.99  --qbf_split                             512
% 3.85/0.99  
% 3.85/0.99  ------ BMC1 Options
% 3.85/0.99  
% 3.85/0.99  --bmc1_incremental                      false
% 3.85/0.99  --bmc1_axioms                           reachable_all
% 3.85/0.99  --bmc1_min_bound                        0
% 3.85/0.99  --bmc1_max_bound                        -1
% 3.85/0.99  --bmc1_max_bound_default                -1
% 3.85/0.99  --bmc1_symbol_reachability              true
% 3.85/0.99  --bmc1_property_lemmas                  false
% 3.85/0.99  --bmc1_k_induction                      false
% 3.85/0.99  --bmc1_non_equiv_states                 false
% 3.85/0.99  --bmc1_deadlock                         false
% 3.85/0.99  --bmc1_ucm                              false
% 3.85/0.99  --bmc1_add_unsat_core                   none
% 3.85/0.99  --bmc1_unsat_core_children              false
% 3.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.99  --bmc1_out_stat                         full
% 3.85/0.99  --bmc1_ground_init                      false
% 3.85/0.99  --bmc1_pre_inst_next_state              false
% 3.85/0.99  --bmc1_pre_inst_state                   false
% 3.85/0.99  --bmc1_pre_inst_reach_state             false
% 3.85/0.99  --bmc1_out_unsat_core                   false
% 3.85/0.99  --bmc1_aig_witness_out                  false
% 3.85/0.99  --bmc1_verbose                          false
% 3.85/0.99  --bmc1_dump_clauses_tptp                false
% 3.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.99  --bmc1_dump_file                        -
% 3.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.99  --bmc1_ucm_extend_mode                  1
% 3.85/0.99  --bmc1_ucm_init_mode                    2
% 3.85/0.99  --bmc1_ucm_cone_mode                    none
% 3.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.99  --bmc1_ucm_relax_model                  4
% 3.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.99  --bmc1_ucm_layered_model                none
% 3.85/0.99  --bmc1_ucm_max_lemma_size               10
% 3.85/0.99  
% 3.85/0.99  ------ AIG Options
% 3.85/0.99  
% 3.85/0.99  --aig_mode                              false
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation Options
% 3.85/0.99  
% 3.85/0.99  --instantiation_flag                    true
% 3.85/0.99  --inst_sos_flag                         true
% 3.85/0.99  --inst_sos_phase                        true
% 3.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel_side                     num_symb
% 3.85/0.99  --inst_solver_per_active                1400
% 3.85/0.99  --inst_solver_calls_frac                1.
% 3.85/0.99  --inst_passive_queue_type               priority_queues
% 3.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.99  --inst_passive_queues_freq              [25;2]
% 3.85/0.99  --inst_dismatching                      true
% 3.85/0.99  --inst_eager_unprocessed_to_passive     true
% 3.85/0.99  --inst_prop_sim_given                   true
% 3.85/0.99  --inst_prop_sim_new                     false
% 3.85/0.99  --inst_subs_new                         false
% 3.85/0.99  --inst_eq_res_simp                      false
% 3.85/0.99  --inst_subs_given                       false
% 3.85/0.99  --inst_orphan_elimination               true
% 3.85/0.99  --inst_learning_loop_flag               true
% 3.85/0.99  --inst_learning_start                   3000
% 3.85/0.99  --inst_learning_factor                  2
% 3.85/0.99  --inst_start_prop_sim_after_learn       3
% 3.85/0.99  --inst_sel_renew                        solver
% 3.85/0.99  --inst_lit_activity_flag                true
% 3.85/0.99  --inst_restr_to_given                   false
% 3.85/0.99  --inst_activity_threshold               500
% 3.85/0.99  --inst_out_proof                        true
% 3.85/0.99  
% 3.85/0.99  ------ Resolution Options
% 3.85/0.99  
% 3.85/0.99  --resolution_flag                       true
% 3.85/0.99  --res_lit_sel                           adaptive
% 3.85/0.99  --res_lit_sel_side                      none
% 3.85/0.99  --res_ordering                          kbo
% 3.85/0.99  --res_to_prop_solver                    active
% 3.85/0.99  --res_prop_simpl_new                    false
% 3.85/0.99  --res_prop_simpl_given                  true
% 3.85/0.99  --res_passive_queue_type                priority_queues
% 3.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.99  --res_passive_queues_freq               [15;5]
% 3.85/0.99  --res_forward_subs                      full
% 3.85/0.99  --res_backward_subs                     full
% 3.85/0.99  --res_forward_subs_resolution           true
% 3.85/0.99  --res_backward_subs_resolution          true
% 3.85/0.99  --res_orphan_elimination                true
% 3.85/0.99  --res_time_limit                        2.
% 3.85/0.99  --res_out_proof                         true
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Options
% 3.85/0.99  
% 3.85/0.99  --superposition_flag                    true
% 3.85/0.99  --sup_passive_queue_type                priority_queues
% 3.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.99  --demod_completeness_check              fast
% 3.85/0.99  --demod_use_ground                      true
% 3.85/0.99  --sup_to_prop_solver                    passive
% 3.85/0.99  --sup_prop_simpl_new                    true
% 3.85/0.99  --sup_prop_simpl_given                  true
% 3.85/0.99  --sup_fun_splitting                     true
% 3.85/0.99  --sup_smt_interval                      50000
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Simplification Setup
% 3.85/0.99  
% 3.85/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.99  --sup_immed_triv                        [TrivRules]
% 3.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_bw_main                     []
% 3.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_input_bw                          []
% 3.85/0.99  
% 3.85/0.99  ------ Combination Options
% 3.85/0.99  
% 3.85/0.99  --comb_res_mult                         3
% 3.85/0.99  --comb_sup_mult                         2
% 3.85/0.99  --comb_inst_mult                        10
% 3.85/0.99  
% 3.85/0.99  ------ Debug Options
% 3.85/0.99  
% 3.85/0.99  --dbg_backtrace                         false
% 3.85/0.99  --dbg_dump_prop_clauses                 false
% 3.85/0.99  --dbg_dump_prop_clauses_file            -
% 3.85/0.99  --dbg_out_stat                          false
% 3.85/0.99  ------ Parsing...
% 3.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.99  ------ Proving...
% 3.85/0.99  ------ Problem Properties 
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  clauses                                 25
% 3.85/0.99  conjectures                             2
% 3.85/0.99  EPR                                     3
% 3.85/0.99  Horn                                    16
% 3.85/0.99  unary                                   2
% 3.85/0.99  binary                                  14
% 3.85/0.99  lits                                    58
% 3.85/0.99  lits eq                                 10
% 3.85/0.99  fd_pure                                 0
% 3.85/0.99  fd_pseudo                               0
% 3.85/0.99  fd_cond                                 0
% 3.85/0.99  fd_pseudo_cond                          5
% 3.85/0.99  AC symbols                              0
% 3.85/0.99  
% 3.85/0.99  ------ Schedule dynamic 5 is on 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  Current options:
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options
% 3.85/0.99  
% 3.85/0.99  --out_options                           all
% 3.85/0.99  --tptp_safe_out                         true
% 3.85/0.99  --problem_path                          ""
% 3.85/0.99  --include_path                          ""
% 3.85/0.99  --clausifier                            res/vclausify_rel
% 3.85/0.99  --clausifier_options                    ""
% 3.85/0.99  --stdin                                 false
% 3.85/0.99  --stats_out                             all
% 3.85/0.99  
% 3.85/0.99  ------ General Options
% 3.85/0.99  
% 3.85/0.99  --fof                                   false
% 3.85/0.99  --time_out_real                         305.
% 3.85/0.99  --time_out_virtual                      -1.
% 3.85/0.99  --symbol_type_check                     false
% 3.85/0.99  --clausify_out                          false
% 3.85/0.99  --sig_cnt_out                           false
% 3.85/0.99  --trig_cnt_out                          false
% 3.85/0.99  --trig_cnt_out_tolerance                1.
% 3.85/0.99  --trig_cnt_out_sk_spl                   false
% 3.85/0.99  --abstr_cl_out                          false
% 3.85/0.99  
% 3.85/0.99  ------ Global Options
% 3.85/0.99  
% 3.85/0.99  --schedule                              default
% 3.85/0.99  --add_important_lit                     false
% 3.85/0.99  --prop_solver_per_cl                    1000
% 3.85/0.99  --min_unsat_core                        false
% 3.85/0.99  --soft_assumptions                      false
% 3.85/0.99  --soft_lemma_size                       3
% 3.85/0.99  --prop_impl_unit_size                   0
% 3.85/0.99  --prop_impl_unit                        []
% 3.85/0.99  --share_sel_clauses                     true
% 3.85/0.99  --reset_solvers                         false
% 3.85/0.99  --bc_imp_inh                            [conj_cone]
% 3.85/0.99  --conj_cone_tolerance                   3.
% 3.85/0.99  --extra_neg_conj                        none
% 3.85/0.99  --large_theory_mode                     true
% 3.85/0.99  --prolific_symb_bound                   200
% 3.85/0.99  --lt_threshold                          2000
% 3.85/0.99  --clause_weak_htbl                      true
% 3.85/0.99  --gc_record_bc_elim                     false
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing Options
% 3.85/0.99  
% 3.85/0.99  --preprocessing_flag                    true
% 3.85/0.99  --time_out_prep_mult                    0.1
% 3.85/0.99  --splitting_mode                        input
% 3.85/0.99  --splitting_grd                         true
% 3.85/0.99  --splitting_cvd                         false
% 3.85/0.99  --splitting_cvd_svl                     false
% 3.85/0.99  --splitting_nvd                         32
% 3.85/0.99  --sub_typing                            true
% 3.85/0.99  --prep_gs_sim                           true
% 3.85/0.99  --prep_unflatten                        true
% 3.85/0.99  --prep_res_sim                          true
% 3.85/0.99  --prep_upred                            true
% 3.85/0.99  --prep_sem_filter                       exhaustive
% 3.85/0.99  --prep_sem_filter_out                   false
% 3.85/0.99  --pred_elim                             true
% 3.85/0.99  --res_sim_input                         true
% 3.85/0.99  --eq_ax_congr_red                       true
% 3.85/0.99  --pure_diseq_elim                       true
% 3.85/0.99  --brand_transform                       false
% 3.85/0.99  --non_eq_to_eq                          false
% 3.85/0.99  --prep_def_merge                        true
% 3.85/0.99  --prep_def_merge_prop_impl              false
% 3.85/0.99  --prep_def_merge_mbd                    true
% 3.85/0.99  --prep_def_merge_tr_red                 false
% 3.85/0.99  --prep_def_merge_tr_cl                  false
% 3.85/0.99  --smt_preprocessing                     true
% 3.85/0.99  --smt_ac_axioms                         fast
% 3.85/0.99  --preprocessed_out                      false
% 3.85/0.99  --preprocessed_stats                    false
% 3.85/0.99  
% 3.85/0.99  ------ Abstraction refinement Options
% 3.85/0.99  
% 3.85/0.99  --abstr_ref                             []
% 3.85/0.99  --abstr_ref_prep                        false
% 3.85/0.99  --abstr_ref_until_sat                   false
% 3.85/0.99  --abstr_ref_sig_restrict                funpre
% 3.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.99  --abstr_ref_under                       []
% 3.85/0.99  
% 3.85/0.99  ------ SAT Options
% 3.85/0.99  
% 3.85/0.99  --sat_mode                              false
% 3.85/0.99  --sat_fm_restart_options                ""
% 3.85/0.99  --sat_gr_def                            false
% 3.85/0.99  --sat_epr_types                         true
% 3.85/0.99  --sat_non_cyclic_types                  false
% 3.85/0.99  --sat_finite_models                     false
% 3.85/0.99  --sat_fm_lemmas                         false
% 3.85/0.99  --sat_fm_prep                           false
% 3.85/0.99  --sat_fm_uc_incr                        true
% 3.85/0.99  --sat_out_model                         small
% 3.85/0.99  --sat_out_clauses                       false
% 3.85/0.99  
% 3.85/0.99  ------ QBF Options
% 3.85/0.99  
% 3.85/0.99  --qbf_mode                              false
% 3.85/0.99  --qbf_elim_univ                         false
% 3.85/0.99  --qbf_dom_inst                          none
% 3.85/0.99  --qbf_dom_pre_inst                      false
% 3.85/0.99  --qbf_sk_in                             false
% 3.85/0.99  --qbf_pred_elim                         true
% 3.85/0.99  --qbf_split                             512
% 3.85/0.99  
% 3.85/0.99  ------ BMC1 Options
% 3.85/0.99  
% 3.85/0.99  --bmc1_incremental                      false
% 3.85/0.99  --bmc1_axioms                           reachable_all
% 3.85/0.99  --bmc1_min_bound                        0
% 3.85/0.99  --bmc1_max_bound                        -1
% 3.85/0.99  --bmc1_max_bound_default                -1
% 3.85/0.99  --bmc1_symbol_reachability              true
% 3.85/0.99  --bmc1_property_lemmas                  false
% 3.85/0.99  --bmc1_k_induction                      false
% 3.85/0.99  --bmc1_non_equiv_states                 false
% 3.85/0.99  --bmc1_deadlock                         false
% 3.85/0.99  --bmc1_ucm                              false
% 3.85/0.99  --bmc1_add_unsat_core                   none
% 3.85/0.99  --bmc1_unsat_core_children              false
% 3.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.99  --bmc1_out_stat                         full
% 3.85/0.99  --bmc1_ground_init                      false
% 3.85/0.99  --bmc1_pre_inst_next_state              false
% 3.85/0.99  --bmc1_pre_inst_state                   false
% 3.85/0.99  --bmc1_pre_inst_reach_state             false
% 3.85/0.99  --bmc1_out_unsat_core                   false
% 3.85/0.99  --bmc1_aig_witness_out                  false
% 3.85/0.99  --bmc1_verbose                          false
% 3.85/0.99  --bmc1_dump_clauses_tptp                false
% 3.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.99  --bmc1_dump_file                        -
% 3.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.99  --bmc1_ucm_extend_mode                  1
% 3.85/0.99  --bmc1_ucm_init_mode                    2
% 3.85/0.99  --bmc1_ucm_cone_mode                    none
% 3.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.99  --bmc1_ucm_relax_model                  4
% 3.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.99  --bmc1_ucm_layered_model                none
% 3.85/0.99  --bmc1_ucm_max_lemma_size               10
% 3.85/0.99  
% 3.85/0.99  ------ AIG Options
% 3.85/0.99  
% 3.85/0.99  --aig_mode                              false
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation Options
% 3.85/0.99  
% 3.85/0.99  --instantiation_flag                    true
% 3.85/0.99  --inst_sos_flag                         true
% 3.85/0.99  --inst_sos_phase                        true
% 3.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.99  --inst_lit_sel_side                     none
% 3.85/0.99  --inst_solver_per_active                1400
% 3.85/0.99  --inst_solver_calls_frac                1.
% 3.85/0.99  --inst_passive_queue_type               priority_queues
% 3.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.99  --inst_passive_queues_freq              [25;2]
% 3.85/0.99  --inst_dismatching                      true
% 3.85/0.99  --inst_eager_unprocessed_to_passive     true
% 3.85/0.99  --inst_prop_sim_given                   true
% 3.85/0.99  --inst_prop_sim_new                     false
% 3.85/0.99  --inst_subs_new                         false
% 3.85/0.99  --inst_eq_res_simp                      false
% 3.85/0.99  --inst_subs_given                       false
% 3.85/0.99  --inst_orphan_elimination               true
% 3.85/0.99  --inst_learning_loop_flag               true
% 3.85/0.99  --inst_learning_start                   3000
% 3.85/0.99  --inst_learning_factor                  2
% 3.85/0.99  --inst_start_prop_sim_after_learn       3
% 3.85/0.99  --inst_sel_renew                        solver
% 3.85/0.99  --inst_lit_activity_flag                true
% 3.85/0.99  --inst_restr_to_given                   false
% 3.85/0.99  --inst_activity_threshold               500
% 3.85/0.99  --inst_out_proof                        true
% 3.85/0.99  
% 3.85/0.99  ------ Resolution Options
% 3.85/0.99  
% 3.85/0.99  --resolution_flag                       false
% 3.85/0.99  --res_lit_sel                           adaptive
% 3.85/0.99  --res_lit_sel_side                      none
% 3.85/0.99  --res_ordering                          kbo
% 3.85/0.99  --res_to_prop_solver                    active
% 3.85/0.99  --res_prop_simpl_new                    false
% 3.85/0.99  --res_prop_simpl_given                  true
% 3.85/0.99  --res_passive_queue_type                priority_queues
% 3.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.99  --res_passive_queues_freq               [15;5]
% 3.85/0.99  --res_forward_subs                      full
% 3.85/0.99  --res_backward_subs                     full
% 3.85/0.99  --res_forward_subs_resolution           true
% 3.85/0.99  --res_backward_subs_resolution          true
% 3.85/0.99  --res_orphan_elimination                true
% 3.85/0.99  --res_time_limit                        2.
% 3.85/0.99  --res_out_proof                         true
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Options
% 3.85/0.99  
% 3.85/0.99  --superposition_flag                    true
% 3.85/0.99  --sup_passive_queue_type                priority_queues
% 3.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.99  --demod_completeness_check              fast
% 3.85/0.99  --demod_use_ground                      true
% 3.85/0.99  --sup_to_prop_solver                    passive
% 3.85/0.99  --sup_prop_simpl_new                    true
% 3.85/0.99  --sup_prop_simpl_given                  true
% 3.85/0.99  --sup_fun_splitting                     true
% 3.85/0.99  --sup_smt_interval                      50000
% 3.85/0.99  
% 3.85/0.99  ------ Superposition Simplification Setup
% 3.85/0.99  
% 3.85/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.99  --sup_immed_triv                        [TrivRules]
% 3.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_immed_bw_main                     []
% 3.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.99  --sup_input_bw                          []
% 3.85/0.99  
% 3.85/0.99  ------ Combination Options
% 3.85/0.99  
% 3.85/0.99  --comb_res_mult                         3
% 3.85/0.99  --comb_sup_mult                         2
% 3.85/0.99  --comb_inst_mult                        10
% 3.85/0.99  
% 3.85/0.99  ------ Debug Options
% 3.85/0.99  
% 3.85/0.99  --dbg_backtrace                         false
% 3.85/0.99  --dbg_dump_prop_clauses                 false
% 3.85/0.99  --dbg_dump_prop_clauses_file            -
% 3.85/0.99  --dbg_out_stat                          false
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ Proving...
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS status Theorem for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  fof(f4,axiom,(
% 3.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f13,plain,(
% 3.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(rectify,[],[f4])).
% 3.85/0.99  
% 3.85/0.99  fof(f16,plain,(
% 3.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(ennf_transformation,[],[f13])).
% 3.85/0.99  
% 3.85/0.99  fof(f31,plain,(
% 3.85/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f32,plain,(
% 3.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).
% 3.85/0.99  
% 3.85/0.99  fof(f53,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  fof(f11,conjecture,(
% 3.85/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f12,negated_conjecture,(
% 3.85/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 3.85/0.99    inference(negated_conjecture,[],[f11])).
% 3.85/0.99  
% 3.85/0.99  fof(f21,plain,(
% 3.85/0.99    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f12])).
% 3.85/0.99  
% 3.85/0.99  fof(f38,plain,(
% 3.85/0.99    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.99    inference(nnf_transformation,[],[f21])).
% 3.85/0.99  
% 3.85/0.99  fof(f39,plain,(
% 3.85/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.99    inference(flattening,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f41,plain,(
% 3.85/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(X1,k3_subset_1(X0,sK6)) | ~r1_xboole_0(X1,sK6)) & (r1_tarski(X1,k3_subset_1(X0,sK6)) | r1_xboole_0(X1,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(X0)))) )),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f40,plain,(
% 3.85/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK5,k3_subset_1(sK4,X2)) | ~r1_xboole_0(sK5,X2)) & (r1_tarski(sK5,k3_subset_1(sK4,X2)) | r1_xboole_0(sK5,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f42,plain,(
% 3.85/0.99    ((~r1_tarski(sK5,k3_subset_1(sK4,sK6)) | ~r1_xboole_0(sK5,sK6)) & (r1_tarski(sK5,k3_subset_1(sK4,sK6)) | r1_xboole_0(sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f41,f40])).
% 3.85/0.99  
% 3.85/0.99  fof(f70,plain,(
% 3.85/0.99    r1_tarski(sK5,k3_subset_1(sK4,sK6)) | r1_xboole_0(sK5,sK6)),
% 3.85/0.99    inference(cnf_transformation,[],[f42])).
% 3.85/0.99  
% 3.85/0.99  fof(f1,axiom,(
% 3.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f14,plain,(
% 3.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f1])).
% 3.85/0.99  
% 3.85/0.99  fof(f22,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(nnf_transformation,[],[f14])).
% 3.85/0.99  
% 3.85/0.99  fof(f23,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(rectify,[],[f22])).
% 3.85/0.99  
% 3.85/0.99  fof(f24,plain,(
% 3.85/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f25,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.85/0.99  
% 3.85/0.99  fof(f44,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f25])).
% 3.85/0.99  
% 3.85/0.99  fof(f43,plain,(
% 3.85/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f25])).
% 3.85/0.99  
% 3.85/0.99  fof(f9,axiom,(
% 3.85/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f20,plain,(
% 3.85/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f9])).
% 3.85/0.99  
% 3.85/0.99  fof(f66,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f20])).
% 3.85/0.99  
% 3.85/0.99  fof(f5,axiom,(
% 3.85/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f56,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f5])).
% 3.85/0.99  
% 3.85/0.99  fof(f79,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(definition_unfolding,[],[f66,f56])).
% 3.85/0.99  
% 3.85/0.99  fof(f69,plain,(
% 3.85/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK4))),
% 3.85/0.99    inference(cnf_transformation,[],[f42])).
% 3.85/0.99  
% 3.85/0.99  fof(f2,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f26,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(nnf_transformation,[],[f2])).
% 3.85/0.99  
% 3.85/0.99  fof(f27,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(flattening,[],[f26])).
% 3.85/0.99  
% 3.85/0.99  fof(f28,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(rectify,[],[f27])).
% 3.85/0.99  
% 3.85/0.99  fof(f29,plain,(
% 3.85/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f30,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.85/0.99  
% 3.85/0.99  fof(f46,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f77,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.85/0.99    inference(definition_unfolding,[],[f46,f56])).
% 3.85/0.99  
% 3.85/0.99  fof(f82,plain,(
% 3.85/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.85/0.99    inference(equality_resolution,[],[f77])).
% 3.85/0.99  
% 3.85/0.99  fof(f8,axiom,(
% 3.85/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f19,plain,(
% 3.85/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f8])).
% 3.85/0.99  
% 3.85/0.99  fof(f37,plain,(
% 3.85/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.85/0.99    inference(nnf_transformation,[],[f19])).
% 3.85/0.99  
% 3.85/0.99  fof(f62,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f37])).
% 3.85/0.99  
% 3.85/0.99  fof(f68,plain,(
% 3.85/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.85/0.99    inference(cnf_transformation,[],[f42])).
% 3.85/0.99  
% 3.85/0.99  fof(f10,axiom,(
% 3.85/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f67,plain,(
% 3.85/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f10])).
% 3.85/0.99  
% 3.85/0.99  fof(f7,axiom,(
% 3.85/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f33,plain,(
% 3.85/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.85/0.99    inference(nnf_transformation,[],[f7])).
% 3.85/0.99  
% 3.85/0.99  fof(f34,plain,(
% 3.85/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.85/0.99    inference(rectify,[],[f33])).
% 3.85/0.99  
% 3.85/0.99  fof(f35,plain,(
% 3.85/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f36,plain,(
% 3.85/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 3.85/0.99  
% 3.85/0.99  fof(f58,plain,(
% 3.85/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.85/0.99    inference(cnf_transformation,[],[f36])).
% 3.85/0.99  
% 3.85/0.99  fof(f84,plain,(
% 3.85/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(equality_resolution,[],[f58])).
% 3.85/0.99  
% 3.85/0.99  fof(f6,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f17,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(ennf_transformation,[],[f6])).
% 3.85/0.99  
% 3.85/0.99  fof(f18,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.99    inference(flattening,[],[f17])).
% 3.85/0.99  
% 3.85/0.99  fof(f57,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f18])).
% 3.85/0.99  
% 3.85/0.99  fof(f78,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f57,f56])).
% 3.85/0.99  
% 3.85/0.99  fof(f71,plain,(
% 3.85/0.99    ~r1_tarski(sK5,k3_subset_1(sK4,sK6)) | ~r1_xboole_0(sK5,sK6)),
% 3.85/0.99    inference(cnf_transformation,[],[f42])).
% 3.85/0.99  
% 3.85/0.99  fof(f48,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f75,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.85/0.99    inference(definition_unfolding,[],[f48,f56])).
% 3.85/0.99  
% 3.85/0.99  fof(f80,plain,(
% 3.85/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.85/0.99    inference(equality_resolution,[],[f75])).
% 3.85/0.99  
% 3.85/0.99  fof(f45,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f25])).
% 3.85/0.99  
% 3.85/0.99  fof(f54,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  fof(f47,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f76,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.85/0.99    inference(definition_unfolding,[],[f47,f56])).
% 3.85/0.99  
% 3.85/0.99  fof(f81,plain,(
% 3.85/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.85/0.99    inference(equality_resolution,[],[f76])).
% 3.85/0.99  
% 3.85/0.99  fof(f3,axiom,(
% 3.85/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f15,plain,(
% 3.85/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.85/0.99    inference(ennf_transformation,[],[f3])).
% 3.85/0.99  
% 3.85/0.99  fof(f52,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f15])).
% 3.85/0.99  
% 3.85/0.99  cnf(c_12,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1201,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_25,negated_conjecture,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) | r1_tarski(sK5,k3_subset_1(sK4,sK6)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1194,plain,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) = iProver_top
% 3.85/0.99      | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1212,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1211,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.85/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2405,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.85/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1212,c_1211]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_22,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_26,negated_conjecture,
% 3.85/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK4)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_420,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.85/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 3.85/0.99      | sK6 != X1 ),
% 3.85/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_421,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK6)) = k3_subset_1(X0,sK6)
% 3.85/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 3.85/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1301,plain,
% 3.85/0.99      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK6)) = k3_subset_1(sK4,sK6) ),
% 3.85/0.99      inference(equality_resolution,[status(thm)],[c_421]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8,plain,
% 3.85/0.99      ( r2_hidden(X0,X1)
% 3.85/0.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1205,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2151,plain,
% 3.85/0.99      ( r2_hidden(X0,k3_subset_1(sK4,sK6)) != iProver_top
% 3.85/0.99      | r2_hidden(X0,sK4) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1301,c_1205]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11385,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),sK4) = iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.85/0.99      | r1_tarski(X0,k3_subset_1(sK4,sK6)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2405,c_2151]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_12679,plain,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) = iProver_top
% 3.85/0.99      | r2_hidden(sK0(sK5,X0),sK4) = iProver_top
% 3.85/0.99      | r1_tarski(sK5,X0) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1194,c_11385]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_21,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_27,negated_conjecture,
% 3.85/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_407,plain,
% 3.85/0.99      ( r2_hidden(X0,X1)
% 3.85/0.99      | v1_xboole_0(X1)
% 3.85/0.99      | k1_zfmisc_1(sK4) != X1
% 3.85/0.99      | sK5 != X0 ),
% 3.85/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_408,plain,
% 3.85/0.99      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 3.85/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_23,plain,
% 3.85/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_414,plain,
% 3.85/0.99      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_408,c_23]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1192,plain,
% 3.85/0.99      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_17,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1196,plain,
% 3.85/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1664,plain,
% 3.85/0.99      ( r1_tarski(sK5,sK4) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1192,c_1196]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_13,plain,
% 3.85/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.85/0.99      | ~ r1_tarski(X0,X2)
% 3.85/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1200,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.85/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3395,plain,
% 3.85/0.99      ( r1_xboole_0(X0,sK6) != iProver_top
% 3.85/0.99      | r1_tarski(X0,k3_subset_1(sK4,sK6)) = iProver_top
% 3.85/0.99      | r1_tarski(X0,sK4) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1301,c_1200]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_24,negated_conjecture,
% 3.85/0.99      ( ~ r1_xboole_0(sK5,sK6) | ~ r1_tarski(sK5,k3_subset_1(sK4,sK6)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1195,plain,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) != iProver_top
% 3.85/0.99      | r1_tarski(sK5,k3_subset_1(sK4,sK6)) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3583,plain,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) != iProver_top
% 3.85/0.99      | r1_tarski(sK5,sK4) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3395,c_1195]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14381,plain,
% 3.85/0.99      ( r2_hidden(sK0(sK5,X0),sK4) = iProver_top
% 3.85/0.99      | r1_tarski(sK5,X0) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_12679,c_1664,c_3583]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1)
% 3.85/0.99      | r2_hidden(X0,X2)
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1207,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3378,plain,
% 3.85/0.99      ( r2_hidden(X0,k3_subset_1(sK4,sK6)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK6) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1301,c_1207]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_0,plain,
% 3.85/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1213,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3957,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,k3_subset_1(sK4,sK6)),sK6) = iProver_top
% 3.85/0.99      | r2_hidden(sK0(X0,k3_subset_1(sK4,sK6)),sK4) != iProver_top
% 3.85/0.99      | r1_tarski(X0,k3_subset_1(sK4,sK6)) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3378,c_1213]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14387,plain,
% 3.85/0.99      ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK6)),sK6) = iProver_top
% 3.85/0.99      | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_14381,c_3957]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_30,plain,
% 3.85/0.99      ( r1_xboole_0(sK5,sK6) = iProver_top
% 3.85/0.99      | r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14662,plain,
% 3.85/0.99      ( r1_tarski(sK5,k3_subset_1(sK4,sK6)) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_14387,c_30,c_1664,c_3583]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1202,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2406,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(sK2(X0,X1),X2) = iProver_top
% 3.85/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1202,c_1211]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1)
% 3.85/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1206,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2384,plain,
% 3.85/0.99      ( r2_hidden(X0,k3_subset_1(sK4,sK6)) != iProver_top
% 3.85/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1301,c_1206]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14601,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(sK2(X0,X1),sK6) != iProver_top
% 3.85/0.99      | r1_tarski(X1,k3_subset_1(sK4,sK6)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2406,c_2384]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15478,plain,
% 3.85/0.99      ( r1_xboole_0(X0,sK5) = iProver_top
% 3.85/0.99      | r2_hidden(sK2(X0,sK5),sK6) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_14662,c_14601]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15525,plain,
% 3.85/0.99      ( r1_xboole_0(sK6,sK5) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1201,c_15478]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_9,plain,
% 3.85/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1288,plain,
% 3.85/0.99      ( ~ r1_xboole_0(sK6,sK5) | r1_xboole_0(sK5,sK6) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1289,plain,
% 3.85/0.99      ( r1_xboole_0(sK6,sK5) != iProver_top
% 3.85/0.99      | r1_xboole_0(sK5,sK6) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(contradiction,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(minisat,[status(thm)],[c_15525,c_3583,c_1664,c_1289]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ General
% 3.85/0.99  
% 3.85/0.99  abstr_ref_over_cycles:                  0
% 3.85/0.99  abstr_ref_under_cycles:                 0
% 3.85/0.99  gc_basic_clause_elim:                   0
% 3.85/0.99  forced_gc_time:                         0
% 3.85/0.99  parsing_time:                           0.008
% 3.85/0.99  unif_index_cands_time:                  0.
% 3.85/0.99  unif_index_add_time:                    0.
% 3.85/0.99  orderings_time:                         0.
% 3.85/0.99  out_proof_time:                         0.008
% 3.85/0.99  total_time:                             0.439
% 3.85/0.99  num_of_symbols:                         47
% 3.85/0.99  num_of_terms:                           15722
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing
% 3.85/0.99  
% 3.85/0.99  num_of_splits:                          0
% 3.85/0.99  num_of_split_atoms:                     0
% 3.85/0.99  num_of_reused_defs:                     0
% 3.85/0.99  num_eq_ax_congr_red:                    34
% 3.85/0.99  num_of_sem_filtered_clauses:            1
% 3.85/0.99  num_of_subtypes:                        0
% 3.85/0.99  monotx_restored_types:                  0
% 3.85/0.99  sat_num_of_epr_types:                   0
% 3.85/0.99  sat_num_of_non_cyclic_types:            0
% 3.85/0.99  sat_guarded_non_collapsed_types:        0
% 3.85/0.99  num_pure_diseq_elim:                    0
% 3.85/0.99  simp_replaced_by:                       0
% 3.85/0.99  res_preprocessed:                       122
% 3.85/0.99  prep_upred:                             0
% 3.85/0.99  prep_unflattend:                        14
% 3.85/0.99  smt_new_axioms:                         0
% 3.85/0.99  pred_elim_cands:                        3
% 3.85/0.99  pred_elim:                              2
% 3.85/0.99  pred_elim_cl:                           3
% 3.85/0.99  pred_elim_cycles:                       4
% 3.85/0.99  merged_defs:                            16
% 3.85/0.99  merged_defs_ncl:                        0
% 3.85/0.99  bin_hyper_res:                          17
% 3.85/0.99  prep_cycles:                            4
% 3.85/0.99  pred_elim_time:                         0.002
% 3.85/0.99  splitting_time:                         0.
% 3.85/0.99  sem_filter_time:                        0.
% 3.85/0.99  monotx_time:                            0.001
% 3.85/0.99  subtype_inf_time:                       0.
% 3.85/0.99  
% 3.85/0.99  ------ Problem properties
% 3.85/0.99  
% 3.85/0.99  clauses:                                25
% 3.85/0.99  conjectures:                            2
% 3.85/0.99  epr:                                    3
% 3.85/0.99  horn:                                   16
% 3.85/0.99  ground:                                 4
% 3.85/0.99  unary:                                  2
% 3.85/0.99  binary:                                 14
% 3.85/0.99  lits:                                   58
% 3.85/0.99  lits_eq:                                10
% 3.85/0.99  fd_pure:                                0
% 3.85/0.99  fd_pseudo:                              0
% 3.85/0.99  fd_cond:                                0
% 3.85/0.99  fd_pseudo_cond:                         5
% 3.85/0.99  ac_symbols:                             0
% 3.85/0.99  
% 3.85/0.99  ------ Propositional Solver
% 3.85/0.99  
% 3.85/0.99  prop_solver_calls:                      30
% 3.85/0.99  prop_fast_solver_calls:                 928
% 3.85/0.99  smt_solver_calls:                       0
% 3.85/0.99  smt_fast_solver_calls:                  0
% 3.85/0.99  prop_num_of_clauses:                    6106
% 3.85/0.99  prop_preprocess_simplified:             14672
% 3.85/0.99  prop_fo_subsumed:                       12
% 3.85/0.99  prop_solver_time:                       0.
% 3.85/0.99  smt_solver_time:                        0.
% 3.85/0.99  smt_fast_solver_time:                   0.
% 3.85/0.99  prop_fast_solver_time:                  0.
% 3.85/0.99  prop_unsat_core_time:                   0.
% 3.85/0.99  
% 3.85/0.99  ------ QBF
% 3.85/0.99  
% 3.85/0.99  qbf_q_res:                              0
% 3.85/0.99  qbf_num_tautologies:                    0
% 3.85/0.99  qbf_prep_cycles:                        0
% 3.85/0.99  
% 3.85/0.99  ------ BMC1
% 3.85/0.99  
% 3.85/0.99  bmc1_current_bound:                     -1
% 3.85/0.99  bmc1_last_solved_bound:                 -1
% 3.85/0.99  bmc1_unsat_core_size:                   -1
% 3.85/0.99  bmc1_unsat_core_parents_size:           -1
% 3.85/0.99  bmc1_merge_next_fun:                    0
% 3.85/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.85/0.99  
% 3.85/0.99  ------ Instantiation
% 3.85/0.99  
% 3.85/0.99  inst_num_of_clauses:                    1516
% 3.85/0.99  inst_num_in_passive:                    755
% 3.85/0.99  inst_num_in_active:                     534
% 3.85/0.99  inst_num_in_unprocessed:                227
% 3.85/0.99  inst_num_of_loops:                      670
% 3.85/0.99  inst_num_of_learning_restarts:          0
% 3.85/0.99  inst_num_moves_active_passive:          135
% 3.85/0.99  inst_lit_activity:                      0
% 3.85/0.99  inst_lit_activity_moves:                0
% 3.85/0.99  inst_num_tautologies:                   0
% 3.85/0.99  inst_num_prop_implied:                  0
% 3.85/0.99  inst_num_existing_simplified:           0
% 3.85/0.99  inst_num_eq_res_simplified:             0
% 3.85/0.99  inst_num_child_elim:                    0
% 3.85/0.99  inst_num_of_dismatching_blockings:      3020
% 3.85/0.99  inst_num_of_non_proper_insts:           1517
% 3.85/0.99  inst_num_of_duplicates:                 0
% 3.85/0.99  inst_inst_num_from_inst_to_res:         0
% 3.85/0.99  inst_dismatching_checking_time:         0.
% 3.85/0.99  
% 3.85/0.99  ------ Resolution
% 3.85/0.99  
% 3.85/0.99  res_num_of_clauses:                     0
% 3.85/0.99  res_num_in_passive:                     0
% 3.85/0.99  res_num_in_active:                      0
% 3.85/0.99  res_num_of_loops:                       126
% 3.85/0.99  res_forward_subset_subsumed:            75
% 3.85/0.99  res_backward_subset_subsumed:           0
% 3.85/0.99  res_forward_subsumed:                   3
% 3.85/0.99  res_backward_subsumed:                  0
% 3.85/0.99  res_forward_subsumption_resolution:     3
% 3.85/0.99  res_backward_subsumption_resolution:    0
% 3.85/0.99  res_clause_to_clause_subsumption:       1366
% 3.85/0.99  res_orphan_elimination:                 0
% 3.85/0.99  res_tautology_del:                      183
% 3.85/0.99  res_num_eq_res_simplified:              0
% 3.85/0.99  res_num_sel_changes:                    0
% 3.85/0.99  res_moves_from_active_to_pass:          0
% 3.85/0.99  
% 3.85/0.99  ------ Superposition
% 3.85/0.99  
% 3.85/0.99  sup_time_total:                         0.
% 3.85/0.99  sup_time_generating:                    0.
% 3.85/0.99  sup_time_sim_full:                      0.
% 3.85/0.99  sup_time_sim_immed:                     0.
% 3.85/0.99  
% 3.85/0.99  sup_num_of_clauses:                     376
% 3.85/0.99  sup_num_in_active:                      129
% 3.85/0.99  sup_num_in_passive:                     247
% 3.85/0.99  sup_num_of_loops:                       133
% 3.85/0.99  sup_fw_superposition:                   194
% 3.85/0.99  sup_bw_superposition:                   261
% 3.85/0.99  sup_immediate_simplified:               49
% 3.85/0.99  sup_given_eliminated:                   0
% 3.85/0.99  comparisons_done:                       0
% 3.85/0.99  comparisons_avoided:                    2
% 3.85/0.99  
% 3.85/0.99  ------ Simplifications
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  sim_fw_subset_subsumed:                 7
% 3.85/0.99  sim_bw_subset_subsumed:                 8
% 3.85/0.99  sim_fw_subsumed:                        24
% 3.85/0.99  sim_bw_subsumed:                        1
% 3.85/0.99  sim_fw_subsumption_res:                 0
% 3.85/0.99  sim_bw_subsumption_res:                 0
% 3.85/0.99  sim_tautology_del:                      16
% 3.85/0.99  sim_eq_tautology_del:                   3
% 3.85/0.99  sim_eq_res_simp:                        1
% 3.85/0.99  sim_fw_demodulated:                     13
% 3.85/0.99  sim_bw_demodulated:                     0
% 3.85/0.99  sim_light_normalised:                   14
% 3.85/0.99  sim_joinable_taut:                      0
% 3.85/0.99  sim_joinable_simp:                      0
% 3.85/0.99  sim_ac_normalised:                      0
% 3.85/0.99  sim_smt_subsumption:                    0
% 3.85/0.99  
%------------------------------------------------------------------------------
