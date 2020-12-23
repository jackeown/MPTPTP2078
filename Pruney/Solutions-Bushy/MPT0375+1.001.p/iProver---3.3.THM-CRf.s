%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0375+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:08 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 199 expanded)
%              Number of clauses        :   47 (  60 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 (1066 expanded)
%              Number of equality atoms :  161 ( 392 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( k1_xboole_0 != X0
                 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X3,X0) )
     => ( ~ m1_subset_1(k1_enumset1(X1,X2,sK6),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k1_enumset1(X1,sK5,X3),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(sK4,X2,X3),k1_zfmisc_1(sK3))
              & k1_xboole_0 != sK3
              & m1_subset_1(X3,sK3) )
          & m1_subset_1(X2,sK3) )
      & m1_subset_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ m1_subset_1(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK6,sK3)
    & m1_subset_1(sK5,sK3)
    & m1_subset_1(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f32,f31,f30])).

fof(f59,plain,(
    ~ m1_subset_1(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    m1_subset_1(sK6,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f65,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f64])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1081,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1087,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2849,plain,
    ( sK2(k1_enumset1(X0,X1,X2),X3) = X0
    | sK2(k1_enumset1(X0,X1,X2),X3) = X1
    | sK2(k1_enumset1(X0,X1,X2),X3) = X2
    | r1_tarski(k1_enumset1(X0,X1,X2),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1087])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1084,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_142,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_20])).

cnf(c_143,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_enumset1(sK4,sK5,sK6) != X0
    | k1_zfmisc_1(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_21])).

cnf(c_331,plain,
    ( ~ r2_hidden(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_1077,plain,
    ( r2_hidden(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_1938,plain,
    ( r1_tarski(k1_enumset1(sK4,sK5,sK6),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1084,c_1077])).

cnf(c_8475,plain,
    ( sK2(k1_enumset1(sK4,sK5,sK6),sK3) = sK6
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) = sK5
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_2849,c_1938])).

cnf(c_606,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1428,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,X2)
    | X1 != X2
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_2186,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK4,X0)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_2188,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK4,sK3)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_1418,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,X2)
    | X1 != X2
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_2130,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK5,X0)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK5
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_2132,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK5,sK3)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_1412,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,X2)
    | X1 != X2
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_2074,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK6,X0)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK6
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_2076,plain,
    ( r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3)
    | ~ r2_hidden(sK6,sK3)
    | sK2(k1_enumset1(sK4,sK5,sK6),sK3) != sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1370,plain,
    ( r1_tarski(k1_enumset1(sK4,sK5,sK6),sK3)
    | ~ r2_hidden(sK2(k1_enumset1(sK4,sK5,sK6),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1254,plain,
    ( ~ r1_tarski(k1_enumset1(sK4,sK5,sK6),sK3)
    | r2_hidden(k1_enumset1(sK4,sK5,sK6),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_382,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_383,plain,
    ( r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_369,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_370,plain,
    ( r2_hidden(sK5,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_347,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_348,plain,
    ( r2_hidden(sK6,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_69,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_66,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_34,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8475,c_2188,c_2132,c_2076,c_1370,c_1254,c_383,c_370,c_348,c_331,c_69,c_66,c_34,c_22])).


%------------------------------------------------------------------------------
