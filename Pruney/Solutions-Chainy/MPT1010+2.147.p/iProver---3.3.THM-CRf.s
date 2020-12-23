%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:30 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 774 expanded)
%              Number of clauses        :   42 ( 113 expanded)
%              Number of leaves         :   19 ( 210 expanded)
%              Depth                    :   24
%              Number of atoms          :  364 (2326 expanded)
%              Number of equality atoms :  154 ( 928 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK6,sK5) != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_funct_1(sK6,sK5) != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f32])).

fof(f58,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f75,plain,(
    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f81,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f30])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f51,f67,f67,f67])).

fof(f82,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f73])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_635,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_203,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_204,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ v1_funct_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_208,plain,
    ( r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK6,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_20])).

cnf(c_209,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK6,X0),X2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X1
    | sK6 != sK6
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_209])).

cnf(c_237,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_237])).

cnf(c_623,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_767,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK5,sK3)
    | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_804,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_funct_1(sK6,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_808,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_17,c_16,c_767,c_804])).

cnf(c_628,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_993,plain,
    ( sK4 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_628])).

cnf(c_2454,plain,
    ( sK0(X0,X1,k1_xboole_0) = sK4
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_993])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_636,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2900,plain,
    ( sK0(X0,X0,k1_xboole_0) = sK4
    | k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_636])).

cnf(c_365,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_364,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1009,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_365,c_364])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_831,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1)),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_821,plain,
    ( r2_hidden(sK2(k4_xboole_0(X0,X1)),X0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_5,c_14])).

cnf(c_933,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[status(thm)],[c_831,c_821])).

cnf(c_1029,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1009,c_933])).

cnf(c_3819,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_1029])).

cnf(c_11,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1154,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_808,c_11])).

cnf(c_1156,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1154,c_808])).

cnf(c_3823,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3819,c_1156])).

cnf(c_3824,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3823])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.34/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/0.93  
% 3.34/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.93  
% 3.34/0.93  ------  iProver source info
% 3.34/0.93  
% 3.34/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.93  git: non_committed_changes: false
% 3.34/0.93  git: last_make_outside_of_git: false
% 3.34/0.93  
% 3.34/0.93  ------ 
% 3.34/0.93  ------ Parsing...
% 3.34/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.93  
% 3.34/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.34/0.93  
% 3.34/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.93  
% 3.34/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.93  ------ Proving...
% 3.34/0.93  ------ Problem Properties 
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  clauses                                 18
% 3.34/0.93  conjectures                             2
% 3.34/0.93  EPR                                     1
% 3.34/0.93  Horn                                    10
% 3.34/0.93  unary                                   4
% 3.34/0.93  binary                                  5
% 3.34/0.93  lits                                    42
% 3.34/0.93  lits eq                                 18
% 3.34/0.93  fd_pure                                 0
% 3.34/0.93  fd_pseudo                               0
% 3.34/0.93  fd_cond                                 3
% 3.34/0.93  fd_pseudo_cond                          6
% 3.34/0.93  AC symbols                              0
% 3.34/0.93  
% 3.34/0.93  ------ Input Options Time Limit: Unbounded
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  ------ 
% 3.34/0.93  Current options:
% 3.34/0.93  ------ 
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  ------ Proving...
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  % SZS status Theorem for theBenchmark.p
% 3.34/0.93  
% 3.34/0.93   Resolution empty clause
% 3.34/0.93  
% 3.34/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.93  
% 3.34/0.93  fof(f1,axiom,(
% 3.34/0.93    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f20,plain,(
% 3.34/0.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/0.93    inference(nnf_transformation,[],[f1])).
% 3.34/0.93  
% 3.34/0.93  fof(f21,plain,(
% 3.34/0.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/0.93    inference(flattening,[],[f20])).
% 3.34/0.93  
% 3.34/0.93  fof(f22,plain,(
% 3.34/0.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/0.93    inference(rectify,[],[f21])).
% 3.34/0.93  
% 3.34/0.93  fof(f23,plain,(
% 3.34/0.93    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.34/0.93    introduced(choice_axiom,[])).
% 3.34/0.93  
% 3.34/0.93  fof(f24,plain,(
% 3.34/0.93    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.34/0.93  
% 3.34/0.93  fof(f37,plain,(
% 3.34/0.93    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f24])).
% 3.34/0.93  
% 3.34/0.93  fof(f13,conjecture,(
% 3.34/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f14,negated_conjecture,(
% 3.34/0.93    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.34/0.93    inference(negated_conjecture,[],[f13])).
% 3.34/0.93  
% 3.34/0.93  fof(f18,plain,(
% 3.34/0.93    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.34/0.93    inference(ennf_transformation,[],[f14])).
% 3.34/0.93  
% 3.34/0.93  fof(f19,plain,(
% 3.34/0.93    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.34/0.93    inference(flattening,[],[f18])).
% 3.34/0.93  
% 3.34/0.93  fof(f32,plain,(
% 3.34/0.93    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 3.34/0.93    introduced(choice_axiom,[])).
% 3.34/0.93  
% 3.34/0.93  fof(f33,plain,(
% 3.34/0.93    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 3.34/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f32])).
% 3.34/0.93  
% 3.34/0.93  fof(f58,plain,(
% 3.34/0.93    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 3.34/0.93    inference(cnf_transformation,[],[f33])).
% 3.34/0.93  
% 3.34/0.93  fof(f3,axiom,(
% 3.34/0.93    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f44,plain,(
% 3.34/0.93    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f3])).
% 3.34/0.93  
% 3.34/0.93  fof(f4,axiom,(
% 3.34/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f45,plain,(
% 3.34/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f4])).
% 3.34/0.93  
% 3.34/0.93  fof(f5,axiom,(
% 3.34/0.93    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f46,plain,(
% 3.34/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f5])).
% 3.34/0.93  
% 3.34/0.93  fof(f6,axiom,(
% 3.34/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f47,plain,(
% 3.34/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f6])).
% 3.34/0.93  
% 3.34/0.93  fof(f7,axiom,(
% 3.34/0.93    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f48,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f7])).
% 3.34/0.93  
% 3.34/0.93  fof(f8,axiom,(
% 3.34/0.93    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f49,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f8])).
% 3.34/0.93  
% 3.34/0.93  fof(f9,axiom,(
% 3.34/0.93    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f50,plain,(
% 3.34/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f9])).
% 3.34/0.93  
% 3.34/0.93  fof(f62,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f49,f50])).
% 3.34/0.93  
% 3.34/0.93  fof(f63,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f48,f62])).
% 3.34/0.93  
% 3.34/0.93  fof(f64,plain,(
% 3.34/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f47,f63])).
% 3.34/0.93  
% 3.34/0.93  fof(f65,plain,(
% 3.34/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f46,f64])).
% 3.34/0.93  
% 3.34/0.93  fof(f66,plain,(
% 3.34/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f45,f65])).
% 3.34/0.93  
% 3.34/0.93  fof(f67,plain,(
% 3.34/0.93    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f44,f66])).
% 3.34/0.93  
% 3.34/0.93  fof(f75,plain,(
% 3.34/0.93    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 3.34/0.93    inference(definition_unfolding,[],[f58,f67])).
% 3.34/0.93  
% 3.34/0.93  fof(f12,axiom,(
% 3.34/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f16,plain,(
% 3.34/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.34/0.93    inference(ennf_transformation,[],[f12])).
% 3.34/0.93  
% 3.34/0.93  fof(f17,plain,(
% 3.34/0.93    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.34/0.93    inference(flattening,[],[f16])).
% 3.34/0.93  
% 3.34/0.93  fof(f56,plain,(
% 3.34/0.93    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f17])).
% 3.34/0.93  
% 3.34/0.93  fof(f59,plain,(
% 3.34/0.93    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 3.34/0.93    inference(cnf_transformation,[],[f33])).
% 3.34/0.93  
% 3.34/0.93  fof(f74,plain,(
% 3.34/0.93    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 3.34/0.93    inference(definition_unfolding,[],[f59,f67])).
% 3.34/0.93  
% 3.34/0.93  fof(f57,plain,(
% 3.34/0.93    v1_funct_1(sK6)),
% 3.34/0.93    inference(cnf_transformation,[],[f33])).
% 3.34/0.93  
% 3.34/0.93  fof(f60,plain,(
% 3.34/0.93    r2_hidden(sK5,sK3)),
% 3.34/0.93    inference(cnf_transformation,[],[f33])).
% 3.34/0.93  
% 3.34/0.93  fof(f61,plain,(
% 3.34/0.93    k1_funct_1(sK6,sK5) != sK4),
% 3.34/0.93    inference(cnf_transformation,[],[f33])).
% 3.34/0.93  
% 3.34/0.93  fof(f2,axiom,(
% 3.34/0.93    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f25,plain,(
% 3.34/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.34/0.93    inference(nnf_transformation,[],[f2])).
% 3.34/0.93  
% 3.34/0.93  fof(f26,plain,(
% 3.34/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.34/0.93    inference(rectify,[],[f25])).
% 3.34/0.93  
% 3.34/0.93  fof(f27,plain,(
% 3.34/0.93    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.34/0.93    introduced(choice_axiom,[])).
% 3.34/0.93  
% 3.34/0.93  fof(f28,plain,(
% 3.34/0.93    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.34/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.34/0.93  
% 3.34/0.93  fof(f40,plain,(
% 3.34/0.93    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.34/0.93    inference(cnf_transformation,[],[f28])).
% 3.34/0.93  
% 3.34/0.93  fof(f71,plain,(
% 3.34/0.93    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.34/0.93    inference(definition_unfolding,[],[f40,f67])).
% 3.34/0.93  
% 3.34/0.93  fof(f81,plain,(
% 3.34/0.93    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.34/0.93    inference(equality_resolution,[],[f71])).
% 3.34/0.93  
% 3.34/0.93  fof(f38,plain,(
% 3.34/0.93    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f24])).
% 3.34/0.93  
% 3.34/0.93  fof(f35,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.34/0.93    inference(cnf_transformation,[],[f24])).
% 3.34/0.93  
% 3.34/0.93  fof(f77,plain,(
% 3.34/0.93    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.34/0.93    inference(equality_resolution,[],[f35])).
% 3.34/0.93  
% 3.34/0.93  fof(f11,axiom,(
% 3.34/0.93    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f15,plain,(
% 3.34/0.93    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.34/0.93    inference(ennf_transformation,[],[f11])).
% 3.34/0.93  
% 3.34/0.93  fof(f30,plain,(
% 3.34/0.93    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.34/0.93    introduced(choice_axiom,[])).
% 3.34/0.93  
% 3.34/0.93  fof(f31,plain,(
% 3.34/0.93    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.34/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f30])).
% 3.34/0.93  
% 3.34/0.93  fof(f53,plain,(
% 3.34/0.93    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.34/0.93    inference(cnf_transformation,[],[f31])).
% 3.34/0.93  
% 3.34/0.93  fof(f34,plain,(
% 3.34/0.93    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.34/0.93    inference(cnf_transformation,[],[f24])).
% 3.34/0.93  
% 3.34/0.93  fof(f78,plain,(
% 3.34/0.93    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.34/0.93    inference(equality_resolution,[],[f34])).
% 3.34/0.93  
% 3.34/0.93  fof(f10,axiom,(
% 3.34/0.93    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.93  
% 3.34/0.93  fof(f29,plain,(
% 3.34/0.93    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.34/0.93    inference(nnf_transformation,[],[f10])).
% 3.34/0.93  
% 3.34/0.93  fof(f51,plain,(
% 3.34/0.93    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.34/0.93    inference(cnf_transformation,[],[f29])).
% 3.34/0.93  
% 3.34/0.93  fof(f73,plain,(
% 3.34/0.93    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.34/0.93    inference(definition_unfolding,[],[f51,f67,f67,f67])).
% 3.34/0.93  
% 3.34/0.93  fof(f82,plain,(
% 3.34/0.93    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.34/0.93    inference(equality_resolution,[],[f73])).
% 3.34/0.93  
% 3.34/0.93  cnf(c_2,plain,
% 3.34/0.93      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.34/0.93      | k4_xboole_0(X0,X1) = X2 ),
% 3.34/0.93      inference(cnf_transformation,[],[f37]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_635,plain,
% 3.34/0.93      ( k4_xboole_0(X0,X1) = X2
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.34/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_19,negated_conjecture,
% 3.34/0.93      ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.34/0.93      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_15,plain,
% 3.34/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.93      | ~ r2_hidden(X3,X1)
% 3.34/0.93      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.34/0.93      | ~ v1_funct_1(X0)
% 3.34/0.93      | k1_xboole_0 = X2 ),
% 3.34/0.93      inference(cnf_transformation,[],[f56]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_18,negated_conjecture,
% 3.34/0.93      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 3.34/0.93      inference(cnf_transformation,[],[f74]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_203,plain,
% 3.34/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.93      | ~ r2_hidden(X3,X1)
% 3.34/0.93      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.34/0.93      | ~ v1_funct_1(X0)
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.34/0.93      | sK6 != X0
% 3.34/0.93      | k1_xboole_0 = X2 ),
% 3.34/0.93      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_204,plain,
% 3.34/0.93      ( ~ v1_funct_2(sK6,X0,X1)
% 3.34/0.93      | ~ r2_hidden(X2,X0)
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.34/0.93      | ~ v1_funct_1(sK6)
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.34/0.93      | k1_xboole_0 = X1 ),
% 3.34/0.93      inference(unflattening,[status(thm)],[c_203]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_20,negated_conjecture,
% 3.34/0.93      ( v1_funct_1(sK6) ),
% 3.34/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_208,plain,
% 3.34/0.93      ( r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.34/0.93      | ~ r2_hidden(X2,X0)
% 3.34/0.93      | ~ v1_funct_2(sK6,X0,X1)
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.34/0.93      | k1_xboole_0 = X1 ),
% 3.34/0.93      inference(global_propositional_subsumption,[status(thm)],[c_204,c_20]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_209,plain,
% 3.34/0.93      ( ~ v1_funct_2(sK6,X0,X1)
% 3.34/0.93      | ~ r2_hidden(X2,X0)
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.34/0.93      | k1_xboole_0 = X1 ),
% 3.34/0.93      inference(renaming,[status(thm)],[c_208]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_236,plain,
% 3.34/0.93      ( ~ r2_hidden(X0,X1)
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X0),X2)
% 3.34/0.93      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X2
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.34/0.93      | sK3 != X1
% 3.34/0.93      | sK6 != sK6
% 3.34/0.93      | k1_xboole_0 = X2 ),
% 3.34/0.93      inference(resolution_lifted,[status(thm)],[c_19,c_209]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_237,plain,
% 3.34/0.93      ( ~ r2_hidden(X0,sK3)
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.34/0.93      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 3.34/0.93      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.34/0.93      inference(unflattening,[status(thm)],[c_236]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_274,plain,
% 3.34/0.93      ( ~ r2_hidden(X0,sK3)
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.34/0.93      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.34/0.93      inference(equality_resolution_simp,[status(thm)],[c_237]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_623,plain,
% 3.34/0.93      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 3.34/0.93      | r2_hidden(X0,sK3) != iProver_top
% 3.34/0.93      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.34/0.93      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_17,negated_conjecture,
% 3.34/0.93      ( r2_hidden(sK5,sK3) ),
% 3.34/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_16,negated_conjecture,
% 3.34/0.93      ( k1_funct_1(sK6,sK5) != sK4 ),
% 3.34/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_767,plain,
% 3.34/0.93      ( r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.34/0.93      | ~ r2_hidden(sK5,sK3)
% 3.34/0.93      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.34/0.93      inference(instantiation,[status(thm)],[c_274]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_9,plain,
% 3.34/0.93      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.34/0.93      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_804,plain,
% 3.34/0.93      ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.34/0.93      | k1_funct_1(sK6,sK5) = sK4 ),
% 3.34/0.93      inference(instantiation,[status(thm)],[c_9]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_808,plain,
% 3.34/0.93      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.34/0.93      inference(global_propositional_subsumption,
% 3.34/0.93                [status(thm)],
% 3.34/0.93                [c_623,c_17,c_16,c_767,c_804]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_628,plain,
% 3.34/0.93      ( X0 = X1
% 3.34/0.93      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.34/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_993,plain,
% 3.34/0.93      ( sK4 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.34/0.93      inference(superposition,[status(thm)],[c_808,c_628]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_2454,plain,
% 3.34/0.93      ( sK0(X0,X1,k1_xboole_0) = sK4
% 3.34/0.93      | k4_xboole_0(X0,X1) = k1_xboole_0
% 3.34/0.93      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.34/0.93      inference(superposition,[status(thm)],[c_635,c_993]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_1,plain,
% 3.34/0.93      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.34/0.93      | k4_xboole_0(X0,X1) = X2 ),
% 3.34/0.93      inference(cnf_transformation,[],[f38]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_636,plain,
% 3.34/0.93      ( k4_xboole_0(X0,X1) = X2
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.34/0.93      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.34/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_2900,plain,
% 3.34/0.93      ( sK0(X0,X0,k1_xboole_0) = sK4
% 3.34/0.93      | k4_xboole_0(X0,X0) = k1_xboole_0
% 3.34/0.93      | r2_hidden(sK0(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.34/0.93      inference(superposition,[status(thm)],[c_2454,c_636]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_365,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_364,plain,( X0 = X0 ),theory(equality) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_1009,plain,
% 3.34/0.93      ( X0 != X1 | X1 = X0 ),
% 3.34/0.93      inference(resolution,[status(thm)],[c_365,c_364]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_4,plain,
% 3.34/0.93      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.34/0.93      inference(cnf_transformation,[],[f77]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_14,plain,
% 3.34/0.93      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.34/0.93      inference(cnf_transformation,[],[f53]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_831,plain,
% 3.34/0.93      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1)),X1)
% 3.34/0.93      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 3.34/0.93      inference(resolution,[status(thm)],[c_4,c_14]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_5,plain,
% 3.34/0.93      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.34/0.93      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_821,plain,
% 3.34/0.93      ( r2_hidden(sK2(k4_xboole_0(X0,X1)),X0)
% 3.34/0.93      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 3.34/0.93      inference(resolution,[status(thm)],[c_5,c_14]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_933,plain,
% 3.34/0.93      ( k1_xboole_0 = k4_xboole_0(X0,X0) ),
% 3.34/0.93      inference(resolution,[status(thm)],[c_831,c_821]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_1029,plain,
% 3.34/0.93      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.34/0.93      inference(resolution,[status(thm)],[c_1009,c_933]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_3819,plain,
% 3.34/0.93      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.34/0.93      inference(global_propositional_subsumption,[status(thm)],[c_2900,c_1029]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_11,plain,
% 3.34/0.93      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.34/0.93      inference(cnf_transformation,[],[f82]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_1154,plain,
% 3.34/0.93      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.34/0.93      inference(superposition,[status(thm)],[c_808,c_11]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_1156,plain,
% 3.34/0.93      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.34/0.93      inference(light_normalisation,[status(thm)],[c_1154,c_808]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_3823,plain,
% 3.34/0.93      ( k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.93      inference(demodulation,[status(thm)],[c_3819,c_1156]) ).
% 3.34/0.93  
% 3.34/0.93  cnf(c_3824,plain,
% 3.34/0.93      ( $false ),
% 3.34/0.93      inference(equality_resolution_simp,[status(thm)],[c_3823]) ).
% 3.34/0.93  
% 3.34/0.93  
% 3.34/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.93  
% 3.34/0.93  ------                               Statistics
% 3.34/0.93  
% 3.34/0.93  ------ Selected
% 3.34/0.93  
% 3.34/0.93  total_time:                             0.162
% 3.34/0.93  
%------------------------------------------------------------------------------
