%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:47 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 272 expanded)
%              Number of clauses        :   33 (  34 expanded)
%              Number of leaves         :   18 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 ( 686 expanded)
%              Number of equality atoms :   82 ( 231 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK4)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK3,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK3,X1)) )
      & v1_zfmisc_1(sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ~ v1_xboole_0(k3_xboole_0(sK3,sK4))
    & v1_zfmisc_1(sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).

fof(f69,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f76])).

fof(f88,plain,(
    ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_942,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_226,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK3)
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_20])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,sK3)
    | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X0
    | sK3 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_18])).

cnf(c_245,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | sK3 = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_12,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_251,plain,
    ( sK3 = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_245,c_12])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_937,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2688,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_251,c_937])).

cnf(c_9,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_936,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2532,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_936])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_935,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2354,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_935])).

cnf(c_2662,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2532,c_2354])).

cnf(c_3168,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2688,c_2662])).

cnf(c_3170,plain,
    ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_3168])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_943,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3211,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_943])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3211,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.83/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.03  
% 2.83/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/1.03  
% 2.83/1.03  ------  iProver source info
% 2.83/1.03  
% 2.83/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.83/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/1.03  git: non_committed_changes: false
% 2.83/1.03  git: last_make_outside_of_git: false
% 2.83/1.03  
% 2.83/1.03  ------ 
% 2.83/1.03  
% 2.83/1.03  ------ Input Options
% 2.83/1.03  
% 2.83/1.03  --out_options                           all
% 2.83/1.03  --tptp_safe_out                         true
% 2.83/1.03  --problem_path                          ""
% 2.83/1.03  --include_path                          ""
% 2.83/1.03  --clausifier                            res/vclausify_rel
% 2.83/1.03  --clausifier_options                    --mode clausify
% 2.83/1.03  --stdin                                 false
% 2.83/1.03  --stats_out                             all
% 2.83/1.03  
% 2.83/1.03  ------ General Options
% 2.83/1.03  
% 2.83/1.03  --fof                                   false
% 2.83/1.03  --time_out_real                         305.
% 2.83/1.03  --time_out_virtual                      -1.
% 2.83/1.03  --symbol_type_check                     false
% 2.83/1.03  --clausify_out                          false
% 2.83/1.03  --sig_cnt_out                           false
% 2.83/1.03  --trig_cnt_out                          false
% 2.83/1.03  --trig_cnt_out_tolerance                1.
% 2.83/1.03  --trig_cnt_out_sk_spl                   false
% 2.83/1.03  --abstr_cl_out                          false
% 2.83/1.03  
% 2.83/1.03  ------ Global Options
% 2.83/1.03  
% 2.83/1.03  --schedule                              default
% 2.83/1.03  --add_important_lit                     false
% 2.83/1.03  --prop_solver_per_cl                    1000
% 2.83/1.03  --min_unsat_core                        false
% 2.83/1.03  --soft_assumptions                      false
% 2.83/1.03  --soft_lemma_size                       3
% 2.83/1.03  --prop_impl_unit_size                   0
% 2.83/1.03  --prop_impl_unit                        []
% 2.83/1.03  --share_sel_clauses                     true
% 2.83/1.03  --reset_solvers                         false
% 2.83/1.03  --bc_imp_inh                            [conj_cone]
% 2.83/1.03  --conj_cone_tolerance                   3.
% 2.83/1.03  --extra_neg_conj                        none
% 2.83/1.03  --large_theory_mode                     true
% 2.83/1.03  --prolific_symb_bound                   200
% 2.83/1.03  --lt_threshold                          2000
% 2.83/1.03  --clause_weak_htbl                      true
% 2.83/1.03  --gc_record_bc_elim                     false
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing Options
% 2.83/1.03  
% 2.83/1.03  --preprocessing_flag                    true
% 2.83/1.03  --time_out_prep_mult                    0.1
% 2.83/1.03  --splitting_mode                        input
% 2.83/1.03  --splitting_grd                         true
% 2.83/1.03  --splitting_cvd                         false
% 2.83/1.03  --splitting_cvd_svl                     false
% 2.83/1.03  --splitting_nvd                         32
% 2.83/1.03  --sub_typing                            true
% 2.83/1.03  --prep_gs_sim                           true
% 2.83/1.03  --prep_unflatten                        true
% 2.83/1.03  --prep_res_sim                          true
% 2.83/1.03  --prep_upred                            true
% 2.83/1.03  --prep_sem_filter                       exhaustive
% 2.83/1.03  --prep_sem_filter_out                   false
% 2.83/1.03  --pred_elim                             true
% 2.83/1.03  --res_sim_input                         true
% 2.83/1.03  --eq_ax_congr_red                       true
% 2.83/1.03  --pure_diseq_elim                       true
% 2.83/1.03  --brand_transform                       false
% 2.83/1.03  --non_eq_to_eq                          false
% 2.83/1.03  --prep_def_merge                        true
% 2.83/1.03  --prep_def_merge_prop_impl              false
% 2.83/1.03  --prep_def_merge_mbd                    true
% 2.83/1.03  --prep_def_merge_tr_red                 false
% 2.83/1.03  --prep_def_merge_tr_cl                  false
% 2.83/1.03  --smt_preprocessing                     true
% 2.83/1.03  --smt_ac_axioms                         fast
% 2.83/1.03  --preprocessed_out                      false
% 2.83/1.03  --preprocessed_stats                    false
% 2.83/1.03  
% 2.83/1.03  ------ Abstraction refinement Options
% 2.83/1.03  
% 2.83/1.03  --abstr_ref                             []
% 2.83/1.03  --abstr_ref_prep                        false
% 2.83/1.03  --abstr_ref_until_sat                   false
% 2.83/1.03  --abstr_ref_sig_restrict                funpre
% 2.83/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/1.03  --abstr_ref_under                       []
% 2.83/1.03  
% 2.83/1.03  ------ SAT Options
% 2.83/1.03  
% 2.83/1.03  --sat_mode                              false
% 2.83/1.03  --sat_fm_restart_options                ""
% 2.83/1.03  --sat_gr_def                            false
% 2.83/1.03  --sat_epr_types                         true
% 2.83/1.03  --sat_non_cyclic_types                  false
% 2.83/1.03  --sat_finite_models                     false
% 2.83/1.03  --sat_fm_lemmas                         false
% 2.83/1.03  --sat_fm_prep                           false
% 2.83/1.03  --sat_fm_uc_incr                        true
% 2.83/1.03  --sat_out_model                         small
% 2.83/1.03  --sat_out_clauses                       false
% 2.83/1.03  
% 2.83/1.03  ------ QBF Options
% 2.83/1.03  
% 2.83/1.03  --qbf_mode                              false
% 2.83/1.03  --qbf_elim_univ                         false
% 2.83/1.03  --qbf_dom_inst                          none
% 2.83/1.03  --qbf_dom_pre_inst                      false
% 2.83/1.03  --qbf_sk_in                             false
% 2.83/1.03  --qbf_pred_elim                         true
% 2.83/1.03  --qbf_split                             512
% 2.83/1.03  
% 2.83/1.03  ------ BMC1 Options
% 2.83/1.03  
% 2.83/1.03  --bmc1_incremental                      false
% 2.83/1.03  --bmc1_axioms                           reachable_all
% 2.83/1.03  --bmc1_min_bound                        0
% 2.83/1.03  --bmc1_max_bound                        -1
% 2.83/1.03  --bmc1_max_bound_default                -1
% 2.83/1.03  --bmc1_symbol_reachability              true
% 2.83/1.03  --bmc1_property_lemmas                  false
% 2.83/1.03  --bmc1_k_induction                      false
% 2.83/1.03  --bmc1_non_equiv_states                 false
% 2.83/1.03  --bmc1_deadlock                         false
% 2.83/1.03  --bmc1_ucm                              false
% 2.83/1.03  --bmc1_add_unsat_core                   none
% 2.83/1.03  --bmc1_unsat_core_children              false
% 2.83/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/1.03  --bmc1_out_stat                         full
% 2.83/1.03  --bmc1_ground_init                      false
% 2.83/1.03  --bmc1_pre_inst_next_state              false
% 2.83/1.03  --bmc1_pre_inst_state                   false
% 2.83/1.03  --bmc1_pre_inst_reach_state             false
% 2.83/1.03  --bmc1_out_unsat_core                   false
% 2.83/1.03  --bmc1_aig_witness_out                  false
% 2.83/1.03  --bmc1_verbose                          false
% 2.83/1.03  --bmc1_dump_clauses_tptp                false
% 2.83/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.83/1.03  --bmc1_dump_file                        -
% 2.83/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.83/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.83/1.03  --bmc1_ucm_extend_mode                  1
% 2.83/1.03  --bmc1_ucm_init_mode                    2
% 2.83/1.03  --bmc1_ucm_cone_mode                    none
% 2.83/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.83/1.03  --bmc1_ucm_relax_model                  4
% 2.83/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.83/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/1.03  --bmc1_ucm_layered_model                none
% 2.83/1.03  --bmc1_ucm_max_lemma_size               10
% 2.83/1.03  
% 2.83/1.03  ------ AIG Options
% 2.83/1.03  
% 2.83/1.03  --aig_mode                              false
% 2.83/1.03  
% 2.83/1.03  ------ Instantiation Options
% 2.83/1.03  
% 2.83/1.03  --instantiation_flag                    true
% 2.83/1.03  --inst_sos_flag                         false
% 2.83/1.03  --inst_sos_phase                        true
% 2.83/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/1.03  --inst_lit_sel_side                     num_symb
% 2.83/1.03  --inst_solver_per_active                1400
% 2.83/1.03  --inst_solver_calls_frac                1.
% 2.83/1.03  --inst_passive_queue_type               priority_queues
% 2.83/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/1.03  --inst_passive_queues_freq              [25;2]
% 2.83/1.03  --inst_dismatching                      true
% 2.83/1.03  --inst_eager_unprocessed_to_passive     true
% 2.83/1.03  --inst_prop_sim_given                   true
% 2.83/1.03  --inst_prop_sim_new                     false
% 2.83/1.03  --inst_subs_new                         false
% 2.83/1.03  --inst_eq_res_simp                      false
% 2.83/1.03  --inst_subs_given                       false
% 2.83/1.03  --inst_orphan_elimination               true
% 2.83/1.03  --inst_learning_loop_flag               true
% 2.83/1.03  --inst_learning_start                   3000
% 2.83/1.03  --inst_learning_factor                  2
% 2.83/1.03  --inst_start_prop_sim_after_learn       3
% 2.83/1.03  --inst_sel_renew                        solver
% 2.83/1.03  --inst_lit_activity_flag                true
% 2.83/1.03  --inst_restr_to_given                   false
% 2.83/1.03  --inst_activity_threshold               500
% 2.83/1.03  --inst_out_proof                        true
% 2.83/1.03  
% 2.83/1.03  ------ Resolution Options
% 2.83/1.03  
% 2.83/1.03  --resolution_flag                       true
% 2.83/1.03  --res_lit_sel                           adaptive
% 2.83/1.03  --res_lit_sel_side                      none
% 2.83/1.03  --res_ordering                          kbo
% 2.83/1.03  --res_to_prop_solver                    active
% 2.83/1.03  --res_prop_simpl_new                    false
% 2.83/1.03  --res_prop_simpl_given                  true
% 2.83/1.03  --res_passive_queue_type                priority_queues
% 2.83/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/1.03  --res_passive_queues_freq               [15;5]
% 2.83/1.03  --res_forward_subs                      full
% 2.83/1.03  --res_backward_subs                     full
% 2.83/1.03  --res_forward_subs_resolution           true
% 2.83/1.03  --res_backward_subs_resolution          true
% 2.83/1.03  --res_orphan_elimination                true
% 2.83/1.03  --res_time_limit                        2.
% 2.83/1.03  --res_out_proof                         true
% 2.83/1.03  
% 2.83/1.03  ------ Superposition Options
% 2.83/1.03  
% 2.83/1.03  --superposition_flag                    true
% 2.83/1.03  --sup_passive_queue_type                priority_queues
% 2.83/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.83/1.03  --demod_completeness_check              fast
% 2.83/1.03  --demod_use_ground                      true
% 2.83/1.03  --sup_to_prop_solver                    passive
% 2.83/1.03  --sup_prop_simpl_new                    true
% 2.83/1.03  --sup_prop_simpl_given                  true
% 2.83/1.03  --sup_fun_splitting                     false
% 2.83/1.03  --sup_smt_interval                      50000
% 2.83/1.03  
% 2.83/1.03  ------ Superposition Simplification Setup
% 2.83/1.03  
% 2.83/1.03  --sup_indices_passive                   []
% 2.83/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_full_bw                           [BwDemod]
% 2.83/1.03  --sup_immed_triv                        [TrivRules]
% 2.83/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_immed_bw_main                     []
% 2.83/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.03  
% 2.83/1.03  ------ Combination Options
% 2.83/1.03  
% 2.83/1.03  --comb_res_mult                         3
% 2.83/1.03  --comb_sup_mult                         2
% 2.83/1.03  --comb_inst_mult                        10
% 2.83/1.03  
% 2.83/1.03  ------ Debug Options
% 2.83/1.03  
% 2.83/1.03  --dbg_backtrace                         false
% 2.83/1.03  --dbg_dump_prop_clauses                 false
% 2.83/1.03  --dbg_dump_prop_clauses_file            -
% 2.83/1.03  --dbg_out_stat                          false
% 2.83/1.03  ------ Parsing...
% 2.83/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/1.03  ------ Proving...
% 2.83/1.03  ------ Problem Properties 
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  clauses                                 18
% 2.83/1.03  conjectures                             1
% 2.83/1.03  EPR                                     4
% 2.83/1.03  Horn                                    12
% 2.83/1.03  unary                                   6
% 2.83/1.03  binary                                  5
% 2.83/1.03  lits                                    38
% 2.83/1.03  lits eq                                 7
% 2.83/1.03  fd_pure                                 0
% 2.83/1.03  fd_pseudo                               0
% 2.83/1.03  fd_cond                                 0
% 2.83/1.03  fd_pseudo_cond                          5
% 2.83/1.03  AC symbols                              0
% 2.83/1.03  
% 2.83/1.03  ------ Schedule dynamic 5 is on 
% 2.83/1.03  
% 2.83/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  ------ 
% 2.83/1.03  Current options:
% 2.83/1.03  ------ 
% 2.83/1.03  
% 2.83/1.03  ------ Input Options
% 2.83/1.03  
% 2.83/1.03  --out_options                           all
% 2.83/1.03  --tptp_safe_out                         true
% 2.83/1.03  --problem_path                          ""
% 2.83/1.03  --include_path                          ""
% 2.83/1.03  --clausifier                            res/vclausify_rel
% 2.83/1.03  --clausifier_options                    --mode clausify
% 2.83/1.03  --stdin                                 false
% 2.83/1.03  --stats_out                             all
% 2.83/1.03  
% 2.83/1.03  ------ General Options
% 2.83/1.03  
% 2.83/1.03  --fof                                   false
% 2.83/1.03  --time_out_real                         305.
% 2.83/1.03  --time_out_virtual                      -1.
% 2.83/1.03  --symbol_type_check                     false
% 2.83/1.03  --clausify_out                          false
% 2.83/1.03  --sig_cnt_out                           false
% 2.83/1.03  --trig_cnt_out                          false
% 2.83/1.03  --trig_cnt_out_tolerance                1.
% 2.83/1.03  --trig_cnt_out_sk_spl                   false
% 2.83/1.03  --abstr_cl_out                          false
% 2.83/1.03  
% 2.83/1.03  ------ Global Options
% 2.83/1.03  
% 2.83/1.03  --schedule                              default
% 2.83/1.03  --add_important_lit                     false
% 2.83/1.03  --prop_solver_per_cl                    1000
% 2.83/1.03  --min_unsat_core                        false
% 2.83/1.03  --soft_assumptions                      false
% 2.83/1.03  --soft_lemma_size                       3
% 2.83/1.03  --prop_impl_unit_size                   0
% 2.83/1.03  --prop_impl_unit                        []
% 2.83/1.03  --share_sel_clauses                     true
% 2.83/1.03  --reset_solvers                         false
% 2.83/1.03  --bc_imp_inh                            [conj_cone]
% 2.83/1.03  --conj_cone_tolerance                   3.
% 2.83/1.03  --extra_neg_conj                        none
% 2.83/1.03  --large_theory_mode                     true
% 2.83/1.03  --prolific_symb_bound                   200
% 2.83/1.03  --lt_threshold                          2000
% 2.83/1.03  --clause_weak_htbl                      true
% 2.83/1.03  --gc_record_bc_elim                     false
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing Options
% 2.83/1.03  
% 2.83/1.03  --preprocessing_flag                    true
% 2.83/1.03  --time_out_prep_mult                    0.1
% 2.83/1.03  --splitting_mode                        input
% 2.83/1.03  --splitting_grd                         true
% 2.83/1.03  --splitting_cvd                         false
% 2.83/1.03  --splitting_cvd_svl                     false
% 2.83/1.03  --splitting_nvd                         32
% 2.83/1.03  --sub_typing                            true
% 2.83/1.03  --prep_gs_sim                           true
% 2.83/1.03  --prep_unflatten                        true
% 2.83/1.03  --prep_res_sim                          true
% 2.83/1.03  --prep_upred                            true
% 2.83/1.03  --prep_sem_filter                       exhaustive
% 2.83/1.03  --prep_sem_filter_out                   false
% 2.83/1.03  --pred_elim                             true
% 2.83/1.03  --res_sim_input                         true
% 2.83/1.03  --eq_ax_congr_red                       true
% 2.83/1.03  --pure_diseq_elim                       true
% 2.83/1.03  --brand_transform                       false
% 2.83/1.03  --non_eq_to_eq                          false
% 2.83/1.03  --prep_def_merge                        true
% 2.83/1.03  --prep_def_merge_prop_impl              false
% 2.83/1.03  --prep_def_merge_mbd                    true
% 2.83/1.03  --prep_def_merge_tr_red                 false
% 2.83/1.03  --prep_def_merge_tr_cl                  false
% 2.83/1.03  --smt_preprocessing                     true
% 2.83/1.03  --smt_ac_axioms                         fast
% 2.83/1.03  --preprocessed_out                      false
% 2.83/1.03  --preprocessed_stats                    false
% 2.83/1.03  
% 2.83/1.03  ------ Abstraction refinement Options
% 2.83/1.03  
% 2.83/1.03  --abstr_ref                             []
% 2.83/1.03  --abstr_ref_prep                        false
% 2.83/1.03  --abstr_ref_until_sat                   false
% 2.83/1.03  --abstr_ref_sig_restrict                funpre
% 2.83/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/1.03  --abstr_ref_under                       []
% 2.83/1.03  
% 2.83/1.03  ------ SAT Options
% 2.83/1.03  
% 2.83/1.03  --sat_mode                              false
% 2.83/1.03  --sat_fm_restart_options                ""
% 2.83/1.03  --sat_gr_def                            false
% 2.83/1.03  --sat_epr_types                         true
% 2.83/1.03  --sat_non_cyclic_types                  false
% 2.83/1.03  --sat_finite_models                     false
% 2.83/1.03  --sat_fm_lemmas                         false
% 2.83/1.03  --sat_fm_prep                           false
% 2.83/1.03  --sat_fm_uc_incr                        true
% 2.83/1.03  --sat_out_model                         small
% 2.83/1.03  --sat_out_clauses                       false
% 2.83/1.03  
% 2.83/1.03  ------ QBF Options
% 2.83/1.03  
% 2.83/1.03  --qbf_mode                              false
% 2.83/1.03  --qbf_elim_univ                         false
% 2.83/1.03  --qbf_dom_inst                          none
% 2.83/1.03  --qbf_dom_pre_inst                      false
% 2.83/1.03  --qbf_sk_in                             false
% 2.83/1.03  --qbf_pred_elim                         true
% 2.83/1.03  --qbf_split                             512
% 2.83/1.03  
% 2.83/1.03  ------ BMC1 Options
% 2.83/1.03  
% 2.83/1.03  --bmc1_incremental                      false
% 2.83/1.03  --bmc1_axioms                           reachable_all
% 2.83/1.03  --bmc1_min_bound                        0
% 2.83/1.03  --bmc1_max_bound                        -1
% 2.83/1.03  --bmc1_max_bound_default                -1
% 2.83/1.03  --bmc1_symbol_reachability              true
% 2.83/1.03  --bmc1_property_lemmas                  false
% 2.83/1.03  --bmc1_k_induction                      false
% 2.83/1.03  --bmc1_non_equiv_states                 false
% 2.83/1.03  --bmc1_deadlock                         false
% 2.83/1.03  --bmc1_ucm                              false
% 2.83/1.03  --bmc1_add_unsat_core                   none
% 2.83/1.03  --bmc1_unsat_core_children              false
% 2.83/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/1.03  --bmc1_out_stat                         full
% 2.83/1.03  --bmc1_ground_init                      false
% 2.83/1.03  --bmc1_pre_inst_next_state              false
% 2.83/1.03  --bmc1_pre_inst_state                   false
% 2.83/1.03  --bmc1_pre_inst_reach_state             false
% 2.83/1.03  --bmc1_out_unsat_core                   false
% 2.83/1.03  --bmc1_aig_witness_out                  false
% 2.83/1.03  --bmc1_verbose                          false
% 2.83/1.03  --bmc1_dump_clauses_tptp                false
% 2.83/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.83/1.03  --bmc1_dump_file                        -
% 2.83/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.83/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.83/1.03  --bmc1_ucm_extend_mode                  1
% 2.83/1.03  --bmc1_ucm_init_mode                    2
% 2.83/1.03  --bmc1_ucm_cone_mode                    none
% 2.83/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.83/1.03  --bmc1_ucm_relax_model                  4
% 2.83/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.83/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/1.03  --bmc1_ucm_layered_model                none
% 2.83/1.03  --bmc1_ucm_max_lemma_size               10
% 2.83/1.03  
% 2.83/1.03  ------ AIG Options
% 2.83/1.03  
% 2.83/1.03  --aig_mode                              false
% 2.83/1.03  
% 2.83/1.03  ------ Instantiation Options
% 2.83/1.03  
% 2.83/1.03  --instantiation_flag                    true
% 2.83/1.03  --inst_sos_flag                         false
% 2.83/1.03  --inst_sos_phase                        true
% 2.83/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/1.03  --inst_lit_sel_side                     none
% 2.83/1.03  --inst_solver_per_active                1400
% 2.83/1.03  --inst_solver_calls_frac                1.
% 2.83/1.03  --inst_passive_queue_type               priority_queues
% 2.83/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/1.03  --inst_passive_queues_freq              [25;2]
% 2.83/1.03  --inst_dismatching                      true
% 2.83/1.03  --inst_eager_unprocessed_to_passive     true
% 2.83/1.03  --inst_prop_sim_given                   true
% 2.83/1.03  --inst_prop_sim_new                     false
% 2.83/1.03  --inst_subs_new                         false
% 2.83/1.03  --inst_eq_res_simp                      false
% 2.83/1.03  --inst_subs_given                       false
% 2.83/1.03  --inst_orphan_elimination               true
% 2.83/1.03  --inst_learning_loop_flag               true
% 2.83/1.03  --inst_learning_start                   3000
% 2.83/1.03  --inst_learning_factor                  2
% 2.83/1.03  --inst_start_prop_sim_after_learn       3
% 2.83/1.03  --inst_sel_renew                        solver
% 2.83/1.03  --inst_lit_activity_flag                true
% 2.83/1.03  --inst_restr_to_given                   false
% 2.83/1.03  --inst_activity_threshold               500
% 2.83/1.03  --inst_out_proof                        true
% 2.83/1.03  
% 2.83/1.03  ------ Resolution Options
% 2.83/1.03  
% 2.83/1.03  --resolution_flag                       false
% 2.83/1.03  --res_lit_sel                           adaptive
% 2.83/1.03  --res_lit_sel_side                      none
% 2.83/1.03  --res_ordering                          kbo
% 2.83/1.03  --res_to_prop_solver                    active
% 2.83/1.03  --res_prop_simpl_new                    false
% 2.83/1.03  --res_prop_simpl_given                  true
% 2.83/1.03  --res_passive_queue_type                priority_queues
% 2.83/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/1.03  --res_passive_queues_freq               [15;5]
% 2.83/1.03  --res_forward_subs                      full
% 2.83/1.03  --res_backward_subs                     full
% 2.83/1.03  --res_forward_subs_resolution           true
% 2.83/1.03  --res_backward_subs_resolution          true
% 2.83/1.03  --res_orphan_elimination                true
% 2.83/1.03  --res_time_limit                        2.
% 2.83/1.03  --res_out_proof                         true
% 2.83/1.03  
% 2.83/1.03  ------ Superposition Options
% 2.83/1.03  
% 2.83/1.03  --superposition_flag                    true
% 2.83/1.03  --sup_passive_queue_type                priority_queues
% 2.83/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.83/1.03  --demod_completeness_check              fast
% 2.83/1.03  --demod_use_ground                      true
% 2.83/1.03  --sup_to_prop_solver                    passive
% 2.83/1.03  --sup_prop_simpl_new                    true
% 2.83/1.03  --sup_prop_simpl_given                  true
% 2.83/1.03  --sup_fun_splitting                     false
% 2.83/1.03  --sup_smt_interval                      50000
% 2.83/1.03  
% 2.83/1.03  ------ Superposition Simplification Setup
% 2.83/1.03  
% 2.83/1.03  --sup_indices_passive                   []
% 2.83/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_full_bw                           [BwDemod]
% 2.83/1.03  --sup_immed_triv                        [TrivRules]
% 2.83/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_immed_bw_main                     []
% 2.83/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.03  
% 2.83/1.03  ------ Combination Options
% 2.83/1.03  
% 2.83/1.03  --comb_res_mult                         3
% 2.83/1.03  --comb_sup_mult                         2
% 2.83/1.03  --comb_inst_mult                        10
% 2.83/1.03  
% 2.83/1.03  ------ Debug Options
% 2.83/1.03  
% 2.83/1.03  --dbg_backtrace                         false
% 2.83/1.03  --dbg_dump_prop_clauses                 false
% 2.83/1.03  --dbg_dump_prop_clauses_file            -
% 2.83/1.03  --dbg_out_stat                          false
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  ------ Proving...
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  % SZS status Theorem for theBenchmark.p
% 2.83/1.03  
% 2.83/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/1.03  
% 2.83/1.03  fof(f1,axiom,(
% 2.83/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f21,plain,(
% 2.83/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.83/1.03    inference(ennf_transformation,[],[f1])).
% 2.83/1.03  
% 2.83/1.03  fof(f28,plain,(
% 2.83/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.83/1.03    inference(nnf_transformation,[],[f21])).
% 2.83/1.03  
% 2.83/1.03  fof(f29,plain,(
% 2.83/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.83/1.03    inference(rectify,[],[f28])).
% 2.83/1.03  
% 2.83/1.03  fof(f30,plain,(
% 2.83/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.83/1.03    introduced(choice_axiom,[])).
% 2.83/1.03  
% 2.83/1.03  fof(f31,plain,(
% 2.83/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.83/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.83/1.03  
% 2.83/1.03  fof(f44,plain,(
% 2.83/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f31])).
% 2.83/1.03  
% 2.83/1.03  fof(f17,axiom,(
% 2.83/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f24,plain,(
% 2.83/1.03    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.83/1.03    inference(ennf_transformation,[],[f17])).
% 2.83/1.03  
% 2.83/1.03  fof(f25,plain,(
% 2.83/1.03    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.83/1.03    inference(flattening,[],[f24])).
% 2.83/1.03  
% 2.83/1.03  fof(f67,plain,(
% 2.83/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f25])).
% 2.83/1.03  
% 2.83/1.03  fof(f18,conjecture,(
% 2.83/1.03    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f19,negated_conjecture,(
% 2.83/1.03    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.83/1.03    inference(negated_conjecture,[],[f18])).
% 2.83/1.03  
% 2.83/1.03  fof(f26,plain,(
% 2.83/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 2.83/1.03    inference(ennf_transformation,[],[f19])).
% 2.83/1.03  
% 2.83/1.03  fof(f27,plain,(
% 2.83/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.83/1.03    inference(flattening,[],[f26])).
% 2.83/1.03  
% 2.83/1.03  fof(f41,plain,(
% 2.83/1.03    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK4) & ~v1_xboole_0(k3_xboole_0(X0,sK4)))) )),
% 2.83/1.03    introduced(choice_axiom,[])).
% 2.83/1.03  
% 2.83/1.03  fof(f40,plain,(
% 2.83/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK3,X1) & ~v1_xboole_0(k3_xboole_0(sK3,X1))) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3))),
% 2.83/1.03    introduced(choice_axiom,[])).
% 2.83/1.03  
% 2.83/1.03  fof(f42,plain,(
% 2.83/1.03    (~r1_tarski(sK3,sK4) & ~v1_xboole_0(k3_xboole_0(sK3,sK4))) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3)),
% 2.83/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41,f40])).
% 2.83/1.03  
% 2.83/1.03  fof(f69,plain,(
% 2.83/1.03    v1_zfmisc_1(sK3)),
% 2.83/1.03    inference(cnf_transformation,[],[f42])).
% 2.83/1.03  
% 2.83/1.03  fof(f68,plain,(
% 2.83/1.03    ~v1_xboole_0(sK3)),
% 2.83/1.03    inference(cnf_transformation,[],[f42])).
% 2.83/1.03  
% 2.83/1.03  fof(f70,plain,(
% 2.83/1.03    ~v1_xboole_0(k3_xboole_0(sK3,sK4))),
% 2.83/1.03    inference(cnf_transformation,[],[f42])).
% 2.83/1.03  
% 2.83/1.03  fof(f15,axiom,(
% 2.83/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f65,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.83/1.03    inference(cnf_transformation,[],[f15])).
% 2.83/1.03  
% 2.83/1.03  fof(f9,axiom,(
% 2.83/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f59,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f9])).
% 2.83/1.03  
% 2.83/1.03  fof(f10,axiom,(
% 2.83/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f60,plain,(
% 2.83/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f10])).
% 2.83/1.03  
% 2.83/1.03  fof(f11,axiom,(
% 2.83/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f61,plain,(
% 2.83/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f11])).
% 2.83/1.03  
% 2.83/1.03  fof(f12,axiom,(
% 2.83/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f62,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f12])).
% 2.83/1.03  
% 2.83/1.03  fof(f13,axiom,(
% 2.83/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f63,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f13])).
% 2.83/1.03  
% 2.83/1.03  fof(f14,axiom,(
% 2.83/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f64,plain,(
% 2.83/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f14])).
% 2.83/1.03  
% 2.83/1.03  fof(f72,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f63,f64])).
% 2.83/1.03  
% 2.83/1.03  fof(f73,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f62,f72])).
% 2.83/1.03  
% 2.83/1.03  fof(f74,plain,(
% 2.83/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f61,f73])).
% 2.83/1.03  
% 2.83/1.03  fof(f75,plain,(
% 2.83/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f60,f74])).
% 2.83/1.03  
% 2.83/1.03  fof(f76,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f59,f75])).
% 2.83/1.03  
% 2.83/1.03  fof(f77,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.83/1.03    inference(definition_unfolding,[],[f65,f76])).
% 2.83/1.03  
% 2.83/1.03  fof(f88,plain,(
% 2.83/1.03    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))),
% 2.83/1.03    inference(definition_unfolding,[],[f70,f77])).
% 2.83/1.03  
% 2.83/1.03  fof(f6,axiom,(
% 2.83/1.03    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f56,plain,(
% 2.83/1.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f6])).
% 2.83/1.03  
% 2.83/1.03  fof(f86,plain,(
% 2.83/1.03    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 2.83/1.03    inference(definition_unfolding,[],[f56,f77])).
% 2.83/1.03  
% 2.83/1.03  fof(f2,axiom,(
% 2.83/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f32,plain,(
% 2.83/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/1.03    inference(nnf_transformation,[],[f2])).
% 2.83/1.03  
% 2.83/1.03  fof(f33,plain,(
% 2.83/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/1.03    inference(flattening,[],[f32])).
% 2.83/1.03  
% 2.83/1.03  fof(f34,plain,(
% 2.83/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/1.03    inference(rectify,[],[f33])).
% 2.83/1.03  
% 2.83/1.03  fof(f35,plain,(
% 2.83/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.83/1.03    introduced(choice_axiom,[])).
% 2.83/1.03  
% 2.83/1.03  fof(f36,plain,(
% 2.83/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.83/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 2.83/1.03  
% 2.83/1.03  fof(f48,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.83/1.03    inference(cnf_transformation,[],[f36])).
% 2.83/1.03  
% 2.83/1.03  fof(f5,axiom,(
% 2.83/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f55,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.83/1.03    inference(cnf_transformation,[],[f5])).
% 2.83/1.03  
% 2.83/1.03  fof(f78,plain,(
% 2.83/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.83/1.03    inference(definition_unfolding,[],[f55,f77])).
% 2.83/1.03  
% 2.83/1.03  fof(f82,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.83/1.03    inference(definition_unfolding,[],[f48,f78])).
% 2.83/1.03  
% 2.83/1.03  fof(f89,plain,(
% 2.83/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.83/1.03    inference(equality_resolution,[],[f82])).
% 2.83/1.03  
% 2.83/1.03  fof(f3,axiom,(
% 2.83/1.03    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.03  
% 2.83/1.03  fof(f20,plain,(
% 2.83/1.03    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.83/1.03    inference(rectify,[],[f3])).
% 2.83/1.03  
% 2.83/1.03  fof(f52,plain,(
% 2.83/1.03    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.83/1.03    inference(cnf_transformation,[],[f20])).
% 2.83/1.03  
% 2.83/1.03  fof(f85,plain,(
% 2.83/1.03    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.83/1.03    inference(definition_unfolding,[],[f52,f77])).
% 2.83/1.03  
% 2.83/1.03  fof(f47,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.83/1.03    inference(cnf_transformation,[],[f36])).
% 2.83/1.03  
% 2.83/1.03  fof(f83,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.83/1.03    inference(definition_unfolding,[],[f47,f78])).
% 2.83/1.03  
% 2.83/1.03  fof(f90,plain,(
% 2.83/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.83/1.03    inference(equality_resolution,[],[f83])).
% 2.83/1.03  
% 2.83/1.03  fof(f46,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.83/1.03    inference(cnf_transformation,[],[f36])).
% 2.83/1.03  
% 2.83/1.03  fof(f84,plain,(
% 2.83/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.83/1.03    inference(definition_unfolding,[],[f46,f78])).
% 2.83/1.03  
% 2.83/1.03  fof(f91,plain,(
% 2.83/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.83/1.03    inference(equality_resolution,[],[f84])).
% 2.83/1.03  
% 2.83/1.03  fof(f45,plain,(
% 2.83/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.83/1.03    inference(cnf_transformation,[],[f31])).
% 2.83/1.03  
% 2.83/1.03  fof(f71,plain,(
% 2.83/1.03    ~r1_tarski(sK3,sK4)),
% 2.83/1.03    inference(cnf_transformation,[],[f42])).
% 2.83/1.03  
% 2.83/1.03  cnf(c_1,plain,
% 2.83/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.83/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_942,plain,
% 2.83/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.83/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_16,plain,
% 2.83/1.03      ( ~ r1_tarski(X0,X1)
% 2.83/1.03      | v1_xboole_0(X0)
% 2.83/1.03      | v1_xboole_0(X1)
% 2.83/1.03      | ~ v1_zfmisc_1(X1)
% 2.83/1.03      | X1 = X0 ),
% 2.83/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_19,negated_conjecture,
% 2.83/1.03      ( v1_zfmisc_1(sK3) ),
% 2.83/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_221,plain,
% 2.83/1.03      ( ~ r1_tarski(X0,X1)
% 2.83/1.03      | v1_xboole_0(X0)
% 2.83/1.03      | v1_xboole_0(X1)
% 2.83/1.03      | X1 = X0
% 2.83/1.03      | sK3 != X1 ),
% 2.83/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_222,plain,
% 2.83/1.03      ( ~ r1_tarski(X0,sK3)
% 2.83/1.03      | v1_xboole_0(X0)
% 2.83/1.03      | v1_xboole_0(sK3)
% 2.83/1.03      | sK3 = X0 ),
% 2.83/1.03      inference(unflattening,[status(thm)],[c_221]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_20,negated_conjecture,
% 2.83/1.03      ( ~ v1_xboole_0(sK3) ),
% 2.83/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_226,plain,
% 2.83/1.03      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK3) | sK3 = X0 ),
% 2.83/1.03      inference(global_propositional_subsumption,
% 2.83/1.03                [status(thm)],
% 2.83/1.03                [c_222,c_20]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_227,plain,
% 2.83/1.03      ( ~ r1_tarski(X0,sK3) | v1_xboole_0(X0) | sK3 = X0 ),
% 2.83/1.03      inference(renaming,[status(thm)],[c_226]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_18,negated_conjecture,
% 2.83/1.03      ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
% 2.83/1.03      inference(cnf_transformation,[],[f88]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_244,plain,
% 2.83/1.03      ( ~ r1_tarski(X0,sK3)
% 2.83/1.03      | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X0
% 2.83/1.03      | sK3 = X0 ),
% 2.83/1.03      inference(resolution_lifted,[status(thm)],[c_227,c_18]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_245,plain,
% 2.83/1.03      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 2.83/1.03      | sK3 = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.83/1.03      inference(unflattening,[status(thm)],[c_244]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_12,plain,
% 2.83/1.03      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 2.83/1.03      inference(cnf_transformation,[],[f86]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_251,plain,
% 2.83/1.03      ( sK3 = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.83/1.03      inference(forward_subsumption_resolution,
% 2.83/1.03                [status(thm)],
% 2.83/1.03                [c_245,c_12]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_6,plain,
% 2.83/1.03      ( ~ r2_hidden(X0,X1)
% 2.83/1.03      | r2_hidden(X0,X2)
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 2.83/1.03      inference(cnf_transformation,[],[f89]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_937,plain,
% 2.83/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.83/1.03      | r2_hidden(X0,X2) = iProver_top
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_2688,plain,
% 2.83/1.03      ( r2_hidden(X0,k5_xboole_0(sK3,sK3)) = iProver_top
% 2.83/1.03      | r2_hidden(X0,sK4) = iProver_top
% 2.83/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 2.83/1.03      inference(superposition,[status(thm)],[c_251,c_937]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_9,plain,
% 2.83/1.03      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.83/1.03      inference(cnf_transformation,[],[f85]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_7,plain,
% 2.83/1.03      ( ~ r2_hidden(X0,X1)
% 2.83/1.03      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 2.83/1.03      inference(cnf_transformation,[],[f90]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_936,plain,
% 2.83/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_2532,plain,
% 2.83/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.83/1.03      inference(superposition,[status(thm)],[c_9,c_936]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_8,plain,
% 2.83/1.03      ( r2_hidden(X0,X1)
% 2.83/1.03      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 2.83/1.03      inference(cnf_transformation,[],[f91]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_935,plain,
% 2.83/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_2354,plain,
% 2.83/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.83/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.83/1.03      inference(superposition,[status(thm)],[c_9,c_935]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_2662,plain,
% 2.83/1.03      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.83/1.03      inference(global_propositional_subsumption,
% 2.83/1.03                [status(thm)],
% 2.83/1.03                [c_2532,c_2354]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_3168,plain,
% 2.83/1.03      ( r2_hidden(X0,sK4) = iProver_top
% 2.83/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 2.83/1.03      inference(forward_subsumption_resolution,
% 2.83/1.03                [status(thm)],
% 2.83/1.03                [c_2688,c_2662]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_3170,plain,
% 2.83/1.03      ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
% 2.83/1.03      | r1_tarski(sK3,X0) = iProver_top ),
% 2.83/1.03      inference(superposition,[status(thm)],[c_942,c_3168]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_0,plain,
% 2.83/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.83/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_943,plain,
% 2.83/1.03      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.83/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_3211,plain,
% 2.83/1.03      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.83/1.03      inference(superposition,[status(thm)],[c_3170,c_943]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_17,negated_conjecture,
% 2.83/1.03      ( ~ r1_tarski(sK3,sK4) ),
% 2.83/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(c_24,plain,
% 2.83/1.03      ( r1_tarski(sK3,sK4) != iProver_top ),
% 2.83/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.83/1.03  
% 2.83/1.03  cnf(contradiction,plain,
% 2.83/1.03      ( $false ),
% 2.83/1.03      inference(minisat,[status(thm)],[c_3211,c_24]) ).
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/1.03  
% 2.83/1.03  ------                               Statistics
% 2.83/1.03  
% 2.83/1.03  ------ General
% 2.83/1.03  
% 2.83/1.03  abstr_ref_over_cycles:                  0
% 2.83/1.03  abstr_ref_under_cycles:                 0
% 2.83/1.03  gc_basic_clause_elim:                   0
% 2.83/1.03  forced_gc_time:                         0
% 2.83/1.03  parsing_time:                           0.008
% 2.83/1.03  unif_index_cands_time:                  0.
% 2.83/1.03  unif_index_add_time:                    0.
% 2.83/1.03  orderings_time:                         0.
% 2.83/1.03  out_proof_time:                         0.011
% 2.83/1.03  total_time:                             0.139
% 2.83/1.03  num_of_symbols:                         44
% 2.83/1.03  num_of_terms:                           3187
% 2.83/1.03  
% 2.83/1.03  ------ Preprocessing
% 2.83/1.03  
% 2.83/1.03  num_of_splits:                          0
% 2.83/1.03  num_of_split_atoms:                     0
% 2.83/1.03  num_of_reused_defs:                     0
% 2.83/1.03  num_eq_ax_congr_red:                    24
% 2.83/1.03  num_of_sem_filtered_clauses:            1
% 2.83/1.03  num_of_subtypes:                        0
% 2.83/1.03  monotx_restored_types:                  0
% 2.83/1.03  sat_num_of_epr_types:                   0
% 2.83/1.03  sat_num_of_non_cyclic_types:            0
% 2.83/1.03  sat_guarded_non_collapsed_types:        0
% 2.83/1.03  num_pure_diseq_elim:                    0
% 2.83/1.03  simp_replaced_by:                       0
% 2.83/1.03  res_preprocessed:                       90
% 2.83/1.03  prep_upred:                             0
% 2.83/1.03  prep_unflattend:                        57
% 2.83/1.03  smt_new_axioms:                         0
% 2.83/1.03  pred_elim_cands:                        2
% 2.83/1.03  pred_elim:                              2
% 2.83/1.03  pred_elim_cl:                           3
% 2.83/1.03  pred_elim_cycles:                       4
% 2.83/1.03  merged_defs:                            0
% 2.83/1.03  merged_defs_ncl:                        0
% 2.83/1.03  bin_hyper_res:                          0
% 2.83/1.03  prep_cycles:                            4
% 2.83/1.03  pred_elim_time:                         0.005
% 2.83/1.03  splitting_time:                         0.
% 2.83/1.03  sem_filter_time:                        0.
% 2.83/1.03  monotx_time:                            0.
% 2.83/1.03  subtype_inf_time:                       0.
% 2.83/1.03  
% 2.83/1.03  ------ Problem properties
% 2.83/1.03  
% 2.83/1.03  clauses:                                18
% 2.83/1.03  conjectures:                            1
% 2.83/1.03  epr:                                    4
% 2.83/1.03  horn:                                   12
% 2.83/1.03  ground:                                 2
% 2.83/1.03  unary:                                  6
% 2.83/1.03  binary:                                 5
% 2.83/1.03  lits:                                   38
% 2.83/1.03  lits_eq:                                7
% 2.83/1.03  fd_pure:                                0
% 2.83/1.03  fd_pseudo:                              0
% 2.83/1.03  fd_cond:                                0
% 2.83/1.03  fd_pseudo_cond:                         5
% 2.83/1.03  ac_symbols:                             0
% 2.83/1.03  
% 2.83/1.03  ------ Propositional Solver
% 2.83/1.03  
% 2.83/1.03  prop_solver_calls:                      26
% 2.83/1.03  prop_fast_solver_calls:                 528
% 2.83/1.03  smt_solver_calls:                       0
% 2.83/1.03  smt_fast_solver_calls:                  0
% 2.83/1.03  prop_num_of_clauses:                    1140
% 2.83/1.03  prop_preprocess_simplified:             4755
% 2.83/1.03  prop_fo_subsumed:                       3
% 2.83/1.03  prop_solver_time:                       0.
% 2.83/1.03  smt_solver_time:                        0.
% 2.83/1.03  smt_fast_solver_time:                   0.
% 2.83/1.03  prop_fast_solver_time:                  0.
% 2.83/1.03  prop_unsat_core_time:                   0.
% 2.83/1.03  
% 2.83/1.03  ------ QBF
% 2.83/1.03  
% 2.83/1.03  qbf_q_res:                              0
% 2.83/1.03  qbf_num_tautologies:                    0
% 2.83/1.03  qbf_prep_cycles:                        0
% 2.83/1.03  
% 2.83/1.03  ------ BMC1
% 2.83/1.03  
% 2.83/1.03  bmc1_current_bound:                     -1
% 2.83/1.03  bmc1_last_solved_bound:                 -1
% 2.83/1.03  bmc1_unsat_core_size:                   -1
% 2.83/1.03  bmc1_unsat_core_parents_size:           -1
% 2.83/1.03  bmc1_merge_next_fun:                    0
% 2.83/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.83/1.03  
% 2.83/1.03  ------ Instantiation
% 2.83/1.03  
% 2.83/1.03  inst_num_of_clauses:                    345
% 2.83/1.03  inst_num_in_passive:                    111
% 2.83/1.03  inst_num_in_active:                     129
% 2.83/1.03  inst_num_in_unprocessed:                105
% 2.83/1.03  inst_num_of_loops:                      140
% 2.83/1.03  inst_num_of_learning_restarts:          0
% 2.83/1.03  inst_num_moves_active_passive:          9
% 2.83/1.03  inst_lit_activity:                      0
% 2.83/1.03  inst_lit_activity_moves:                0
% 2.83/1.03  inst_num_tautologies:                   0
% 2.83/1.03  inst_num_prop_implied:                  0
% 2.83/1.03  inst_num_existing_simplified:           0
% 2.83/1.03  inst_num_eq_res_simplified:             0
% 2.83/1.03  inst_num_child_elim:                    0
% 2.83/1.03  inst_num_of_dismatching_blockings:      86
% 2.83/1.03  inst_num_of_non_proper_insts:           191
% 2.83/1.03  inst_num_of_duplicates:                 0
% 2.83/1.03  inst_inst_num_from_inst_to_res:         0
% 2.83/1.03  inst_dismatching_checking_time:         0.
% 2.83/1.03  
% 2.83/1.03  ------ Resolution
% 2.83/1.03  
% 2.83/1.03  res_num_of_clauses:                     0
% 2.83/1.03  res_num_in_passive:                     0
% 2.83/1.03  res_num_in_active:                      0
% 2.83/1.03  res_num_of_loops:                       94
% 2.83/1.03  res_forward_subset_subsumed:            18
% 2.83/1.03  res_backward_subset_subsumed:           2
% 2.83/1.03  res_forward_subsumed:                   0
% 2.83/1.03  res_backward_subsumed:                  1
% 2.83/1.03  res_forward_subsumption_resolution:     1
% 2.83/1.03  res_backward_subsumption_resolution:    0
% 2.83/1.03  res_clause_to_clause_subsumption:       377
% 2.83/1.03  res_orphan_elimination:                 0
% 2.83/1.03  res_tautology_del:                      22
% 2.83/1.03  res_num_eq_res_simplified:              0
% 2.83/1.03  res_num_sel_changes:                    0
% 2.83/1.03  res_moves_from_active_to_pass:          0
% 2.83/1.03  
% 2.83/1.03  ------ Superposition
% 2.83/1.03  
% 2.83/1.03  sup_time_total:                         0.
% 2.83/1.03  sup_time_generating:                    0.
% 2.83/1.03  sup_time_sim_full:                      0.
% 2.83/1.03  sup_time_sim_immed:                     0.
% 2.83/1.03  
% 2.83/1.03  sup_num_of_clauses:                     67
% 2.83/1.03  sup_num_in_active:                      28
% 2.83/1.03  sup_num_in_passive:                     39
% 2.83/1.03  sup_num_of_loops:                       27
% 2.83/1.03  sup_fw_superposition:                   41
% 2.83/1.03  sup_bw_superposition:                   28
% 2.83/1.03  sup_immediate_simplified:               10
% 2.83/1.03  sup_given_eliminated:                   0
% 2.83/1.03  comparisons_done:                       0
% 2.83/1.03  comparisons_avoided:                    0
% 2.83/1.03  
% 2.83/1.03  ------ Simplifications
% 2.83/1.03  
% 2.83/1.03  
% 2.83/1.03  sim_fw_subset_subsumed:                 1
% 2.83/1.03  sim_bw_subset_subsumed:                 4
% 2.83/1.03  sim_fw_subsumed:                        4
% 2.83/1.03  sim_bw_subsumed:                        3
% 2.83/1.03  sim_fw_subsumption_res:                 1
% 2.83/1.03  sim_bw_subsumption_res:                 0
% 2.83/1.03  sim_tautology_del:                      5
% 2.83/1.03  sim_eq_tautology_del:                   1
% 2.83/1.03  sim_eq_res_simp:                        1
% 2.83/1.03  sim_fw_demodulated:                     0
% 2.83/1.03  sim_bw_demodulated:                     0
% 2.83/1.03  sim_light_normalised:                   1
% 2.83/1.03  sim_joinable_taut:                      0
% 2.83/1.03  sim_joinable_simp:                      0
% 2.83/1.03  sim_ac_normalised:                      0
% 2.83/1.03  sim_smt_subsumption:                    0
% 2.83/1.03  
%------------------------------------------------------------------------------
