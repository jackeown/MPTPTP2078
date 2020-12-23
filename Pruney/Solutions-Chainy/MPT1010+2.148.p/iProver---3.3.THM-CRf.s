%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:30 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 774 expanded)
%              Number of clauses        :   42 ( 113 expanded)
%              Number of leaves         :   19 ( 210 expanded)
%              Depth                    :   24
%              Number of atoms          :  364 (2326 expanded)
%              Number of equality atoms :  154 ( 928 expanded)
%              Maximal formula depth    :   12 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_1587,plain,
    ( sK4 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_628])).

cnf(c_2454,plain,
    ( sK0(X0,X1,k1_xboole_0) = sK4
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_1587])).

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

cnf(c_1003,plain,
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

cnf(c_1023,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1003,c_933])).

cnf(c_3819,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_1023])).

cnf(c_11,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1142,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_808,c_11])).

cnf(c_1144,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1142,c_808])).

cnf(c_3823,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3819,c_1144])).

cnf(c_3824,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3823])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.90/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.00  
% 2.90/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/1.00  
% 2.90/1.00  ------  iProver source info
% 2.90/1.00  
% 2.90/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.90/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/1.00  git: non_committed_changes: false
% 2.90/1.00  git: last_make_outside_of_git: false
% 2.90/1.00  
% 2.90/1.00  ------ 
% 2.90/1.00  ------ Parsing...
% 2.90/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/1.00  ------ Proving...
% 2.90/1.00  ------ Problem Properties 
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  clauses                                 18
% 2.90/1.00  conjectures                             2
% 2.90/1.00  EPR                                     1
% 2.90/1.00  Horn                                    10
% 2.90/1.00  unary                                   4
% 2.90/1.00  binary                                  5
% 2.90/1.00  lits                                    42
% 2.90/1.00  lits eq                                 18
% 2.90/1.00  fd_pure                                 0
% 2.90/1.00  fd_pseudo                               0
% 2.90/1.00  fd_cond                                 3
% 2.90/1.00  fd_pseudo_cond                          6
% 2.90/1.00  AC symbols                              0
% 2.90/1.00  
% 2.90/1.00  ------ Input Options Time Limit: Unbounded
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  ------ 
% 2.90/1.00  Current options:
% 2.90/1.00  ------ 
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  ------ Proving...
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  % SZS status Theorem for theBenchmark.p
% 2.90/1.00  
% 2.90/1.00   Resolution empty clause
% 2.90/1.00  
% 2.90/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/1.00  
% 2.90/1.00  fof(f1,axiom,(
% 2.90/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f20,plain,(
% 2.90/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.90/1.00    inference(nnf_transformation,[],[f1])).
% 2.90/1.00  
% 2.90/1.00  fof(f21,plain,(
% 2.90/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.90/1.00    inference(flattening,[],[f20])).
% 2.90/1.00  
% 2.90/1.00  fof(f22,plain,(
% 2.90/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.90/1.00    inference(rectify,[],[f21])).
% 2.90/1.00  
% 2.90/1.00  fof(f23,plain,(
% 2.90/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.90/1.00    introduced(choice_axiom,[])).
% 2.90/1.00  
% 2.90/1.00  fof(f24,plain,(
% 2.90/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.90/1.00  
% 2.90/1.00  fof(f37,plain,(
% 2.90/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f24])).
% 2.90/1.00  
% 2.90/1.00  fof(f13,conjecture,(
% 2.90/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f14,negated_conjecture,(
% 2.90/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.90/1.00    inference(negated_conjecture,[],[f13])).
% 2.90/1.00  
% 2.90/1.00  fof(f18,plain,(
% 2.90/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.90/1.00    inference(ennf_transformation,[],[f14])).
% 2.90/1.00  
% 2.90/1.00  fof(f19,plain,(
% 2.90/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.90/1.00    inference(flattening,[],[f18])).
% 2.90/1.00  
% 2.90/1.00  fof(f32,plain,(
% 2.90/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 2.90/1.00    introduced(choice_axiom,[])).
% 2.90/1.00  
% 2.90/1.00  fof(f33,plain,(
% 2.90/1.00    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 2.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f32])).
% 2.90/1.00  
% 2.90/1.00  fof(f58,plain,(
% 2.90/1.00    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 2.90/1.00    inference(cnf_transformation,[],[f33])).
% 2.90/1.00  
% 2.90/1.00  fof(f3,axiom,(
% 2.90/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f44,plain,(
% 2.90/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f3])).
% 2.90/1.00  
% 2.90/1.00  fof(f4,axiom,(
% 2.90/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f45,plain,(
% 2.90/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f4])).
% 2.90/1.00  
% 2.90/1.00  fof(f5,axiom,(
% 2.90/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f46,plain,(
% 2.90/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f5])).
% 2.90/1.00  
% 2.90/1.00  fof(f6,axiom,(
% 2.90/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f47,plain,(
% 2.90/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f6])).
% 2.90/1.00  
% 2.90/1.00  fof(f7,axiom,(
% 2.90/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f48,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f7])).
% 2.90/1.00  
% 2.90/1.00  fof(f8,axiom,(
% 2.90/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f49,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f8])).
% 2.90/1.00  
% 2.90/1.00  fof(f9,axiom,(
% 2.90/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f50,plain,(
% 2.90/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f9])).
% 2.90/1.00  
% 2.90/1.00  fof(f62,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f49,f50])).
% 2.90/1.00  
% 2.90/1.00  fof(f63,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f48,f62])).
% 2.90/1.00  
% 2.90/1.00  fof(f64,plain,(
% 2.90/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f47,f63])).
% 2.90/1.00  
% 2.90/1.00  fof(f65,plain,(
% 2.90/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f46,f64])).
% 2.90/1.00  
% 2.90/1.00  fof(f66,plain,(
% 2.90/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f45,f65])).
% 2.90/1.00  
% 2.90/1.00  fof(f67,plain,(
% 2.90/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f44,f66])).
% 2.90/1.00  
% 2.90/1.00  fof(f75,plain,(
% 2.90/1.00    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 2.90/1.00    inference(definition_unfolding,[],[f58,f67])).
% 2.90/1.00  
% 2.90/1.00  fof(f12,axiom,(
% 2.90/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f16,plain,(
% 2.90/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.90/1.00    inference(ennf_transformation,[],[f12])).
% 2.90/1.00  
% 2.90/1.00  fof(f17,plain,(
% 2.90/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.90/1.00    inference(flattening,[],[f16])).
% 2.90/1.00  
% 2.90/1.00  fof(f56,plain,(
% 2.90/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f17])).
% 2.90/1.00  
% 2.90/1.00  fof(f59,plain,(
% 2.90/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 2.90/1.00    inference(cnf_transformation,[],[f33])).
% 2.90/1.00  
% 2.90/1.00  fof(f74,plain,(
% 2.90/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 2.90/1.00    inference(definition_unfolding,[],[f59,f67])).
% 2.90/1.00  
% 2.90/1.00  fof(f57,plain,(
% 2.90/1.00    v1_funct_1(sK6)),
% 2.90/1.00    inference(cnf_transformation,[],[f33])).
% 2.90/1.00  
% 2.90/1.00  fof(f60,plain,(
% 2.90/1.00    r2_hidden(sK5,sK3)),
% 2.90/1.00    inference(cnf_transformation,[],[f33])).
% 2.90/1.00  
% 2.90/1.00  fof(f61,plain,(
% 2.90/1.00    k1_funct_1(sK6,sK5) != sK4),
% 2.90/1.00    inference(cnf_transformation,[],[f33])).
% 2.90/1.00  
% 2.90/1.00  fof(f2,axiom,(
% 2.90/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f25,plain,(
% 2.90/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.90/1.00    inference(nnf_transformation,[],[f2])).
% 2.90/1.00  
% 2.90/1.00  fof(f26,plain,(
% 2.90/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.90/1.00    inference(rectify,[],[f25])).
% 2.90/1.00  
% 2.90/1.00  fof(f27,plain,(
% 2.90/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.90/1.00    introduced(choice_axiom,[])).
% 2.90/1.00  
% 2.90/1.00  fof(f28,plain,(
% 2.90/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.90/1.00  
% 2.90/1.00  fof(f40,plain,(
% 2.90/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.90/1.00    inference(cnf_transformation,[],[f28])).
% 2.90/1.00  
% 2.90/1.00  fof(f71,plain,(
% 2.90/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.90/1.00    inference(definition_unfolding,[],[f40,f67])).
% 2.90/1.00  
% 2.90/1.00  fof(f81,plain,(
% 2.90/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.90/1.00    inference(equality_resolution,[],[f71])).
% 2.90/1.00  
% 2.90/1.00  fof(f38,plain,(
% 2.90/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f24])).
% 2.90/1.00  
% 2.90/1.00  fof(f35,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.90/1.00    inference(cnf_transformation,[],[f24])).
% 2.90/1.00  
% 2.90/1.00  fof(f77,plain,(
% 2.90/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.90/1.00    inference(equality_resolution,[],[f35])).
% 2.90/1.00  
% 2.90/1.00  fof(f11,axiom,(
% 2.90/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f15,plain,(
% 2.90/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.90/1.00    inference(ennf_transformation,[],[f11])).
% 2.90/1.00  
% 2.90/1.00  fof(f30,plain,(
% 2.90/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 2.90/1.00    introduced(choice_axiom,[])).
% 2.90/1.00  
% 2.90/1.00  fof(f31,plain,(
% 2.90/1.00    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f30])).
% 2.90/1.00  
% 2.90/1.00  fof(f53,plain,(
% 2.90/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.90/1.00    inference(cnf_transformation,[],[f31])).
% 2.90/1.00  
% 2.90/1.00  fof(f34,plain,(
% 2.90/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.90/1.00    inference(cnf_transformation,[],[f24])).
% 2.90/1.00  
% 2.90/1.00  fof(f78,plain,(
% 2.90/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.90/1.00    inference(equality_resolution,[],[f34])).
% 2.90/1.00  
% 2.90/1.00  fof(f10,axiom,(
% 2.90/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.90/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.00  
% 2.90/1.00  fof(f29,plain,(
% 2.90/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.90/1.00    inference(nnf_transformation,[],[f10])).
% 2.90/1.00  
% 2.90/1.00  fof(f51,plain,(
% 2.90/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.90/1.00    inference(cnf_transformation,[],[f29])).
% 2.90/1.00  
% 2.90/1.00  fof(f73,plain,(
% 2.90/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.90/1.00    inference(definition_unfolding,[],[f51,f67,f67,f67])).
% 2.90/1.00  
% 2.90/1.00  fof(f82,plain,(
% 2.90/1.00    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.90/1.00    inference(equality_resolution,[],[f73])).
% 2.90/1.00  
% 2.90/1.00  cnf(c_2,plain,
% 2.90/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.90/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 2.90/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_635,plain,
% 2.90/1.00      ( k4_xboole_0(X0,X1) = X2
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_19,negated_conjecture,
% 2.90/1.00      ( v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 2.90/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_15,plain,
% 2.90/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.00      | ~ r2_hidden(X3,X1)
% 2.90/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.90/1.00      | ~ v1_funct_1(X0)
% 2.90/1.00      | k1_xboole_0 = X2 ),
% 2.90/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_18,negated_conjecture,
% 2.90/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 2.90/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_203,plain,
% 2.90/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.00      | ~ r2_hidden(X3,X1)
% 2.90/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.90/1.00      | ~ v1_funct_1(X0)
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.90/1.00      | sK6 != X0
% 2.90/1.00      | k1_xboole_0 = X2 ),
% 2.90/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_204,plain,
% 2.90/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 2.90/1.00      | ~ r2_hidden(X2,X0)
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.90/1.00      | ~ v1_funct_1(sK6)
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.90/1.00      | k1_xboole_0 = X1 ),
% 2.90/1.00      inference(unflattening,[status(thm)],[c_203]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_20,negated_conjecture,
% 2.90/1.00      ( v1_funct_1(sK6) ),
% 2.90/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_208,plain,
% 2.90/1.00      ( r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.90/1.00      | ~ r2_hidden(X2,X0)
% 2.90/1.00      | ~ v1_funct_2(sK6,X0,X1)
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.90/1.00      | k1_xboole_0 = X1 ),
% 2.90/1.00      inference(global_propositional_subsumption,[status(thm)],[c_204,c_20]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_209,plain,
% 2.90/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 2.90/1.00      | ~ r2_hidden(X2,X0)
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.90/1.00      | k1_xboole_0 = X1 ),
% 2.90/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_236,plain,
% 2.90/1.00      ( ~ r2_hidden(X0,X1)
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X0),X2)
% 2.90/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X2
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.90/1.00      | sK3 != X1
% 2.90/1.00      | sK6 != sK6
% 2.90/1.00      | k1_xboole_0 = X2 ),
% 2.90/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_209]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_237,plain,
% 2.90/1.00      ( ~ r2_hidden(X0,sK3)
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.90/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 2.90/1.00      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 2.90/1.00      inference(unflattening,[status(thm)],[c_236]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_274,plain,
% 2.90/1.00      ( ~ r2_hidden(X0,sK3)
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.90/1.00      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 2.90/1.00      inference(equality_resolution_simp,[status(thm)],[c_237]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_623,plain,
% 2.90/1.00      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 2.90/1.00      | r2_hidden(X0,sK3) != iProver_top
% 2.90/1.00      | r2_hidden(k1_funct_1(sK6,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_17,negated_conjecture,
% 2.90/1.00      ( r2_hidden(sK5,sK3) ),
% 2.90/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_16,negated_conjecture,
% 2.90/1.00      ( k1_funct_1(sK6,sK5) != sK4 ),
% 2.90/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_767,plain,
% 2.90/1.00      ( r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.90/1.00      | ~ r2_hidden(sK5,sK3)
% 2.90/1.00      | k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_274]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_9,plain,
% 2.90/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.90/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_804,plain,
% 2.90/1.00      ( ~ r2_hidden(k1_funct_1(sK6,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.90/1.00      | k1_funct_1(sK6,sK5) = sK4 ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_808,plain,
% 2.90/1.00      ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 2.90/1.00      inference(global_propositional_subsumption,
% 2.90/1.00                [status(thm)],
% 2.90/1.00                [c_623,c_17,c_16,c_767,c_804]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_628,plain,
% 2.90/1.00      ( X0 = X1
% 2.90/1.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1587,plain,
% 2.90/1.00      ( sK4 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_808,c_628]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_2454,plain,
% 2.90/1.00      ( sK0(X0,X1,k1_xboole_0) = sK4
% 2.90/1.00      | k4_xboole_0(X0,X1) = k1_xboole_0
% 2.90/1.00      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_635,c_1587]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1,plain,
% 2.90/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.90/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 2.90/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_636,plain,
% 2.90/1.00      ( k4_xboole_0(X0,X1) = X2
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 2.90/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_2900,plain,
% 2.90/1.00      ( sK0(X0,X0,k1_xboole_0) = sK4
% 2.90/1.00      | k4_xboole_0(X0,X0) = k1_xboole_0
% 2.90/1.00      | r2_hidden(sK0(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_2454,c_636]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_365,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_364,plain,( X0 = X0 ),theory(equality) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1003,plain,
% 2.90/1.00      ( X0 != X1 | X1 = X0 ),
% 2.90/1.00      inference(resolution,[status(thm)],[c_365,c_364]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4,plain,
% 2.90/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.90/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_14,plain,
% 2.90/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.90/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_831,plain,
% 2.90/1.00      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1)),X1)
% 2.90/1.00      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 2.90/1.00      inference(resolution,[status(thm)],[c_4,c_14]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_5,plain,
% 2.90/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.90/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_821,plain,
% 2.90/1.00      ( r2_hidden(sK2(k4_xboole_0(X0,X1)),X0)
% 2.90/1.00      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 2.90/1.00      inference(resolution,[status(thm)],[c_5,c_14]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_933,plain,
% 2.90/1.00      ( k1_xboole_0 = k4_xboole_0(X0,X0) ),
% 2.90/1.00      inference(resolution,[status(thm)],[c_831,c_821]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1023,plain,
% 2.90/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.90/1.00      inference(resolution,[status(thm)],[c_1003,c_933]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_3819,plain,
% 2.90/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.90/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2900,c_1023]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_11,plain,
% 2.90/1.00      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.90/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1142,plain,
% 2.90/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_808,c_11]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1144,plain,
% 2.90/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.90/1.00      inference(light_normalisation,[status(thm)],[c_1142,c_808]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_3823,plain,
% 2.90/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.90/1.00      inference(demodulation,[status(thm)],[c_3819,c_1144]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_3824,plain,
% 2.90/1.00      ( $false ),
% 2.90/1.00      inference(equality_resolution_simp,[status(thm)],[c_3823]) ).
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/1.00  
% 2.90/1.00  ------                               Statistics
% 2.90/1.00  
% 2.90/1.00  ------ Selected
% 2.90/1.00  
% 2.90/1.00  total_time:                             0.172
% 2.90/1.00  
%------------------------------------------------------------------------------
