%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:35 EST 2020

% Result     : Theorem 15.16s
% Output     : CNFRefutation 15.16s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 391 expanded)
%              Number of clauses        :   73 (  87 expanded)
%              Number of leaves         :   20 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  460 (1229 expanded)
%              Number of equality atoms :  259 ( 744 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f47])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f80,f91])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f113,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f114,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f113])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f111,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f96])).

fof(f112,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f111])).

fof(f13,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f81,f91])).

fof(f122,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f105])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f83,f91,f91])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f117,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f49])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f91])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f115,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f116,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f115])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f79,f91,f91,f91])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f78,f91,f91,f91])).

fof(f121,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f16,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f51])).

fof(f89,plain,(
    k1_setfam_1(k1_tarski(sK6)) != sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) != sK6 ),
    inference(definition_unfolding,[],[f89,f91])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1374,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1352,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4554,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1352])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1375,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_46081,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4554,c_1375])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1365,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1366,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_29,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k1_setfam_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1349,plain,
    ( k1_setfam_1(X0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1782,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1366,c_1349])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1350,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2145,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1350])).

cnf(c_3785,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_2145])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1372,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4069,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_1372])).

cnf(c_46781,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_46081,c_4069])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1353,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_47879,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_46781,c_1353])).

cnf(c_47889,plain,
    ( r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47879])).

cnf(c_678,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6803,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
    | X1 != k2_enumset1(sK6,sK6,sK6,sK6)
    | X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_18885,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
    | X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
    | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_6803])).

cnf(c_18886,plain,
    ( X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
    | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6)
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18885])).

cnf(c_18888,plain,
    ( sK6 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
    | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6)
    | r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18886])).

cnf(c_27,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_8729,plain,
    ( ~ r1_tarski(k2_enumset1(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(sK6,sK6,sK6,sK6))
    | sK6 = sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_31,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6982,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
    | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X1
    | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X2
    | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X3
    | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
    inference(resolution,[status(thm)],[c_13,c_31])).

cnf(c_6984,plain,
    ( r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
    | sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) = sK6
    | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_6982])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6012,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(X0,X0,X0,X0))
    | r1_tarski(k2_enumset1(sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6023,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
    | r1_tarski(k2_enumset1(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_6012])).

cnf(c_677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1685,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK5(X3,X2))
    | X2 != X0
    | sK5(X3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_4053,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6))
    | sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_4054,plain,
    ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != X0
    | sK6 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4053])).

cnf(c_4056,plain,
    ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != sK6
    | sK6 != sK6
    | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4054])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,sK5(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3309,plain,
    ( ~ r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6))
    | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
    | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3310,plain,
    ( k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6)
    | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) != iProver_top
    | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3309])).

cnf(c_1737,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),X1),k2_enumset1(X0,X0,X0,X0))
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2410,plain,
    ( r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
    | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_2411,plain,
    ( r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2410])).

cnf(c_1726,plain,
    ( ~ r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
    | k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1727,plain,
    ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
    | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_1641,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6)
    | ~ r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
    | k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1642,plain,
    ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
    | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) != iProver_top
    | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_1600,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1601,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1600])).

cnf(c_1603,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_1602,plain,
    ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_1600])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_103,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_105,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_90,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_92,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_91,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_62,plain,
    ( k4_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK6,sK6,sK6,sK6)) = k2_enumset1(sK6,sK6,sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_23,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_61,plain,
    ( k4_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK6,sK6,sK6,sK6)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_33,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) != sK6 ),
    inference(cnf_transformation,[],[f108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47889,c_18888,c_8729,c_6984,c_6023,c_4056,c_3310,c_2411,c_2410,c_1727,c_1726,c_1642,c_1641,c_1603,c_1602,c_105,c_92,c_91,c_62,c_61,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.16/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.16/2.49  
% 15.16/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.16/2.49  
% 15.16/2.49  ------  iProver source info
% 15.16/2.49  
% 15.16/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.16/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.16/2.49  git: non_committed_changes: false
% 15.16/2.49  git: last_make_outside_of_git: false
% 15.16/2.49  
% 15.16/2.49  ------ 
% 15.16/2.49  ------ Parsing...
% 15.16/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.16/2.49  
% 15.16/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.16/2.49  
% 15.16/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.16/2.49  
% 15.16/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.16/2.49  ------ Proving...
% 15.16/2.49  ------ Problem Properties 
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  clauses                                 33
% 15.16/2.49  conjectures                             1
% 15.16/2.49  EPR                                     3
% 15.16/2.49  Horn                                    24
% 15.16/2.49  unary                                   7
% 15.16/2.49  binary                                  11
% 15.16/2.49  lits                                    78
% 15.16/2.49  lits eq                                 26
% 15.16/2.49  fd_pure                                 0
% 15.16/2.49  fd_pseudo                               0
% 15.16/2.49  fd_cond                                 2
% 15.16/2.49  fd_pseudo_cond                          11
% 15.16/2.49  AC symbols                              0
% 15.16/2.49  
% 15.16/2.49  ------ Input Options Time Limit: Unbounded
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  ------ 
% 15.16/2.49  Current options:
% 15.16/2.49  ------ 
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  ------ Proving...
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  % SZS status Theorem for theBenchmark.p
% 15.16/2.49  
% 15.16/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.16/2.49  
% 15.16/2.49  fof(f1,axiom,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f18,plain,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.16/2.49    inference(ennf_transformation,[],[f1])).
% 15.16/2.49  
% 15.16/2.49  fof(f28,plain,(
% 15.16/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.16/2.49    inference(nnf_transformation,[],[f18])).
% 15.16/2.49  
% 15.16/2.49  fof(f29,plain,(
% 15.16/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.16/2.49    inference(rectify,[],[f28])).
% 15.16/2.49  
% 15.16/2.49  fof(f30,plain,(
% 15.16/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.16/2.49    introduced(choice_axiom,[])).
% 15.16/2.49  
% 15.16/2.49  fof(f31,plain,(
% 15.16/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.16/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 15.16/2.49  
% 15.16/2.49  fof(f54,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f31])).
% 15.16/2.49  
% 15.16/2.49  fof(f10,axiom,(
% 15.16/2.49    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f47,plain,(
% 15.16/2.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.16/2.49    inference(nnf_transformation,[],[f10])).
% 15.16/2.49  
% 15.16/2.49  fof(f48,plain,(
% 15.16/2.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.16/2.49    inference(flattening,[],[f47])).
% 15.16/2.49  
% 15.16/2.49  fof(f80,plain,(
% 15.16/2.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.16/2.49    inference(cnf_transformation,[],[f48])).
% 15.16/2.49  
% 15.16/2.49  fof(f4,axiom,(
% 15.16/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f67,plain,(
% 15.16/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f4])).
% 15.16/2.49  
% 15.16/2.49  fof(f5,axiom,(
% 15.16/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f68,plain,(
% 15.16/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f5])).
% 15.16/2.49  
% 15.16/2.49  fof(f6,axiom,(
% 15.16/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f69,plain,(
% 15.16/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f6])).
% 15.16/2.49  
% 15.16/2.49  fof(f90,plain,(
% 15.16/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.16/2.49    inference(definition_unfolding,[],[f68,f69])).
% 15.16/2.49  
% 15.16/2.49  fof(f91,plain,(
% 15.16/2.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.16/2.49    inference(definition_unfolding,[],[f67,f90])).
% 15.16/2.49  
% 15.16/2.49  fof(f106,plain,(
% 15.16/2.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 15.16/2.49    inference(definition_unfolding,[],[f80,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f55,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f31])).
% 15.16/2.49  
% 15.16/2.49  fof(f3,axiom,(
% 15.16/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f19,plain,(
% 15.16/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.16/2.49    inference(ennf_transformation,[],[f3])).
% 15.16/2.49  
% 15.16/2.49  fof(f34,plain,(
% 15.16/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.16/2.49    inference(nnf_transformation,[],[f19])).
% 15.16/2.49  
% 15.16/2.49  fof(f35,plain,(
% 15.16/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.16/2.49    inference(flattening,[],[f34])).
% 15.16/2.49  
% 15.16/2.49  fof(f36,plain,(
% 15.16/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.16/2.49    inference(rectify,[],[f35])).
% 15.16/2.49  
% 15.16/2.49  fof(f37,plain,(
% 15.16/2.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 15.16/2.49    introduced(choice_axiom,[])).
% 15.16/2.49  
% 15.16/2.49  fof(f38,plain,(
% 15.16/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.16/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 15.16/2.49  
% 15.16/2.49  fof(f61,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.16/2.49    inference(cnf_transformation,[],[f38])).
% 15.16/2.49  
% 15.16/2.49  fof(f97,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.16/2.49    inference(definition_unfolding,[],[f61,f69])).
% 15.16/2.49  
% 15.16/2.49  fof(f113,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 15.16/2.49    inference(equality_resolution,[],[f97])).
% 15.16/2.49  
% 15.16/2.49  fof(f114,plain,(
% 15.16/2.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 15.16/2.49    inference(equality_resolution,[],[f113])).
% 15.16/2.49  
% 15.16/2.49  fof(f62,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.16/2.49    inference(cnf_transformation,[],[f38])).
% 15.16/2.49  
% 15.16/2.49  fof(f96,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.16/2.49    inference(definition_unfolding,[],[f62,f69])).
% 15.16/2.49  
% 15.16/2.49  fof(f111,plain,(
% 15.16/2.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 15.16/2.49    inference(equality_resolution,[],[f96])).
% 15.16/2.49  
% 15.16/2.49  fof(f112,plain,(
% 15.16/2.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 15.16/2.49    inference(equality_resolution,[],[f111])).
% 15.16/2.49  
% 15.16/2.49  fof(f13,axiom,(
% 15.16/2.49    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f22,plain,(
% 15.16/2.49    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 15.16/2.49    inference(ennf_transformation,[],[f13])).
% 15.16/2.49  
% 15.16/2.49  fof(f85,plain,(
% 15.16/2.49    ( ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f22])).
% 15.16/2.49  
% 15.16/2.49  fof(f12,axiom,(
% 15.16/2.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f21,plain,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 15.16/2.49    inference(ennf_transformation,[],[f12])).
% 15.16/2.49  
% 15.16/2.49  fof(f84,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f21])).
% 15.16/2.49  
% 15.16/2.49  fof(f2,axiom,(
% 15.16/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f32,plain,(
% 15.16/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.16/2.49    inference(nnf_transformation,[],[f2])).
% 15.16/2.49  
% 15.16/2.49  fof(f33,plain,(
% 15.16/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.16/2.49    inference(flattening,[],[f32])).
% 15.16/2.49  
% 15.16/2.49  fof(f58,plain,(
% 15.16/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f33])).
% 15.16/2.49  
% 15.16/2.49  fof(f81,plain,(
% 15.16/2.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.16/2.49    inference(cnf_transformation,[],[f48])).
% 15.16/2.49  
% 15.16/2.49  fof(f105,plain,(
% 15.16/2.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 15.16/2.49    inference(definition_unfolding,[],[f81,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f122,plain,(
% 15.16/2.49    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 15.16/2.49    inference(equality_resolution,[],[f105])).
% 15.16/2.49  
% 15.16/2.49  fof(f11,axiom,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f20,plain,(
% 15.16/2.49    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 15.16/2.49    inference(ennf_transformation,[],[f11])).
% 15.16/2.49  
% 15.16/2.49  fof(f83,plain,(
% 15.16/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 15.16/2.49    inference(cnf_transformation,[],[f20])).
% 15.16/2.49  
% 15.16/2.49  fof(f107,plain,(
% 15.16/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 15.16/2.49    inference(definition_unfolding,[],[f83,f91,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f59,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 15.16/2.49    inference(cnf_transformation,[],[f38])).
% 15.16/2.49  
% 15.16/2.49  fof(f99,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.16/2.49    inference(definition_unfolding,[],[f59,f69])).
% 15.16/2.49  
% 15.16/2.49  fof(f117,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 15.16/2.49    inference(equality_resolution,[],[f99])).
% 15.16/2.49  
% 15.16/2.49  fof(f14,axiom,(
% 15.16/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f23,plain,(
% 15.16/2.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 15.16/2.49    inference(ennf_transformation,[],[f14])).
% 15.16/2.49  
% 15.16/2.49  fof(f24,plain,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 15.16/2.49    inference(flattening,[],[f23])).
% 15.16/2.49  
% 15.16/2.49  fof(f49,plain,(
% 15.16/2.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 15.16/2.49    introduced(choice_axiom,[])).
% 15.16/2.49  
% 15.16/2.49  fof(f50,plain,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 15.16/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f49])).
% 15.16/2.49  
% 15.16/2.49  fof(f86,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f50])).
% 15.16/2.49  
% 15.16/2.49  fof(f8,axiom,(
% 15.16/2.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f45,plain,(
% 15.16/2.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 15.16/2.49    inference(nnf_transformation,[],[f8])).
% 15.16/2.49  
% 15.16/2.49  fof(f77,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.16/2.49    inference(cnf_transformation,[],[f45])).
% 15.16/2.49  
% 15.16/2.49  fof(f100,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.16/2.49    inference(definition_unfolding,[],[f77,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f87,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK5(X0,X1))) )),
% 15.16/2.49    inference(cnf_transformation,[],[f50])).
% 15.16/2.49  
% 15.16/2.49  fof(f56,plain,(
% 15.16/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.16/2.49    inference(cnf_transformation,[],[f33])).
% 15.16/2.49  
% 15.16/2.49  fof(f110,plain,(
% 15.16/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.16/2.49    inference(equality_resolution,[],[f56])).
% 15.16/2.49  
% 15.16/2.49  fof(f60,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.16/2.49    inference(cnf_transformation,[],[f38])).
% 15.16/2.49  
% 15.16/2.49  fof(f98,plain,(
% 15.16/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.16/2.49    inference(definition_unfolding,[],[f60,f69])).
% 15.16/2.49  
% 15.16/2.49  fof(f115,plain,(
% 15.16/2.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 15.16/2.49    inference(equality_resolution,[],[f98])).
% 15.16/2.49  
% 15.16/2.49  fof(f116,plain,(
% 15.16/2.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 15.16/2.49    inference(equality_resolution,[],[f115])).
% 15.16/2.49  
% 15.16/2.49  fof(f9,axiom,(
% 15.16/2.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f46,plain,(
% 15.16/2.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 15.16/2.49    inference(nnf_transformation,[],[f9])).
% 15.16/2.49  
% 15.16/2.49  fof(f79,plain,(
% 15.16/2.49    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 15.16/2.49    inference(cnf_transformation,[],[f46])).
% 15.16/2.49  
% 15.16/2.49  fof(f102,plain,(
% 15.16/2.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 15.16/2.49    inference(definition_unfolding,[],[f79,f91,f91,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f78,plain,(
% 15.16/2.49    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 15.16/2.49    inference(cnf_transformation,[],[f46])).
% 15.16/2.49  
% 15.16/2.49  fof(f103,plain,(
% 15.16/2.49    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 15.16/2.49    inference(definition_unfolding,[],[f78,f91,f91,f91])).
% 15.16/2.49  
% 15.16/2.49  fof(f121,plain,(
% 15.16/2.49    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 15.16/2.49    inference(equality_resolution,[],[f103])).
% 15.16/2.49  
% 15.16/2.49  fof(f16,conjecture,(
% 15.16/2.49    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 15.16/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.16/2.49  
% 15.16/2.49  fof(f17,negated_conjecture,(
% 15.16/2.49    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 15.16/2.49    inference(negated_conjecture,[],[f16])).
% 15.16/2.49  
% 15.16/2.49  fof(f27,plain,(
% 15.16/2.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 15.16/2.49    inference(ennf_transformation,[],[f17])).
% 15.16/2.49  
% 15.16/2.49  fof(f51,plain,(
% 15.16/2.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.16/2.49    introduced(choice_axiom,[])).
% 15.16/2.49  
% 15.16/2.49  fof(f52,plain,(
% 15.16/2.49    k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.16/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f51])).
% 15.16/2.49  
% 15.16/2.49  fof(f89,plain,(
% 15.16/2.49    k1_setfam_1(k1_tarski(sK6)) != sK6),
% 15.16/2.49    inference(cnf_transformation,[],[f52])).
% 15.16/2.49  
% 15.16/2.49  fof(f108,plain,(
% 15.16/2.49    k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) != sK6),
% 15.16/2.49    inference(definition_unfolding,[],[f89,f91])).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1,plain,
% 15.16/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.16/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1374,plain,
% 15.16/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.16/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_26,plain,
% 15.16/2.49      ( r2_hidden(X0,X1)
% 15.16/2.49      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
% 15.16/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1352,plain,
% 15.16/2.49      ( r2_hidden(X0,X1) = iProver_top
% 15.16/2.49      | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_4554,plain,
% 15.16/2.49      ( r2_hidden(sK0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0) = iProver_top
% 15.16/2.49      | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_1374,c_1352]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_0,plain,
% 15.16/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.16/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1375,plain,
% 15.16/2.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.16/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_46081,plain,
% 15.16/2.49      ( r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) = iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_4554,c_1375]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_11,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 15.16/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1365,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_10,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 15.16/2.49      inference(cnf_transformation,[],[f112]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1366,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_29,plain,
% 15.16/2.49      ( ~ r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0 ),
% 15.16/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1349,plain,
% 15.16/2.49      ( k1_setfam_1(X0) = k1_xboole_0
% 15.16/2.49      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1782,plain,
% 15.16/2.49      ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_1366,c_1349]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_28,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 15.16/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1350,plain,
% 15.16/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.16/2.49      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_2145,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
% 15.16/2.49      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_1782,c_1350]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_3785,plain,
% 15.16/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_1365,c_2145]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_3,plain,
% 15.16/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.16/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1372,plain,
% 15.16/2.49      ( X0 = X1
% 15.16/2.49      | r1_tarski(X1,X0) != iProver_top
% 15.16/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_4069,plain,
% 15.16/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_3785,c_1372]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_46781,plain,
% 15.16/2.49      ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_46081,c_4069]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_25,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 15.16/2.49      inference(cnf_transformation,[],[f122]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1353,plain,
% 15.16/2.49      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_47879,plain,
% 15.16/2.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.16/2.49      inference(superposition,[status(thm)],[c_46781,c_1353]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_47889,plain,
% 15.16/2.49      ( r2_hidden(sK6,k1_xboole_0) != iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_47879]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_678,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.16/2.49      theory(equality) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_6803,plain,
% 15.16/2.49      ( r2_hidden(X0,X1)
% 15.16/2.49      | ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | X1 != k2_enumset1(sK6,sK6,sK6,sK6)
% 15.16/2.49      | X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_678]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_18885,plain,
% 15.16/2.49      ( r2_hidden(X0,k1_xboole_0)
% 15.16/2.49      | ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
% 15.16/2.49      | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_6803]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_18886,plain,
% 15.16/2.49      ( X0 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
% 15.16/2.49      | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6)
% 15.16/2.49      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 15.16/2.49      | r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_18885]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_18888,plain,
% 15.16/2.49      ( sK6 != sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
% 15.16/2.49      | k1_xboole_0 != k2_enumset1(sK6,sK6,sK6,sK6)
% 15.16/2.49      | r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
% 15.16/2.49      | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_18886]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_27,plain,
% 15.16/2.49      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
% 15.16/2.49      | X1 = X0 ),
% 15.16/2.49      inference(cnf_transformation,[],[f107]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_8729,plain,
% 15.16/2.49      ( ~ r1_tarski(k2_enumset1(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | sK6 = sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_27]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_13,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 15.16/2.49      | X0 = X1
% 15.16/2.49      | X0 = X2
% 15.16/2.49      | X0 = X3 ),
% 15.16/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_31,plain,
% 15.16/2.49      ( r2_hidden(sK5(X0,X1),X0)
% 15.16/2.49      | r1_tarski(X1,k1_setfam_1(X0))
% 15.16/2.49      | k1_xboole_0 = X0 ),
% 15.16/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_6982,plain,
% 15.16/2.49      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
% 15.16/2.49      | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X1
% 15.16/2.49      | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X2
% 15.16/2.49      | sK5(k2_enumset1(X1,X1,X2,X3),X0) = X3
% 15.16/2.49      | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
% 15.16/2.49      inference(resolution,[status(thm)],[c_13,c_31]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_6984,plain,
% 15.16/2.49      ( r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
% 15.16/2.49      | sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) = sK6
% 15.16/2.49      | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_6982]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_20,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 15.16/2.49      inference(cnf_transformation,[],[f100]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_6012,plain,
% 15.16/2.49      ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(X0,X0,X0,X0))
% 15.16/2.49      | r1_tarski(k2_enumset1(sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(X0,X0,X0,X0)) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_6023,plain,
% 15.16/2.49      ( ~ r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | r1_tarski(k2_enumset1(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))),k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_6012]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_677,plain,
% 15.16/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.16/2.49      theory(equality) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1685,plain,
% 15.16/2.49      ( ~ r1_tarski(X0,X1)
% 15.16/2.49      | r1_tarski(X2,sK5(X3,X2))
% 15.16/2.49      | X2 != X0
% 15.16/2.49      | sK5(X3,X2) != X1 ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_677]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_4053,plain,
% 15.16/2.49      ( ~ r1_tarski(X0,X1)
% 15.16/2.49      | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6))
% 15.16/2.49      | sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != X1
% 15.16/2.49      | sK6 != X0 ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_1685]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_4054,plain,
% 15.16/2.49      ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != X0
% 15.16/2.49      | sK6 != X1
% 15.16/2.49      | r1_tarski(X1,X0) != iProver_top
% 15.16/2.49      | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_4053]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_4056,plain,
% 15.16/2.49      ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6) != sK6
% 15.16/2.49      | sK6 != sK6
% 15.16/2.49      | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) = iProver_top
% 15.16/2.49      | r1_tarski(sK6,sK6) != iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_4054]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_30,plain,
% 15.16/2.49      ( ~ r1_tarski(X0,sK5(X1,X0))
% 15.16/2.49      | r1_tarski(X0,k1_setfam_1(X1))
% 15.16/2.49      | k1_xboole_0 = X1 ),
% 15.16/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_3309,plain,
% 15.16/2.49      ( ~ r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6))
% 15.16/2.49      | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
% 15.16/2.49      | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_30]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_3310,plain,
% 15.16/2.49      ( k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6)
% 15.16/2.49      | r1_tarski(sK6,sK5(k2_enumset1(sK6,sK6,sK6,sK6),sK6)) != iProver_top
% 15.16/2.49      | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_3309]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1737,plain,
% 15.16/2.49      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),X1),k2_enumset1(X0,X0,X0,X0))
% 15.16/2.49      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_2410,plain,
% 15.16/2.49      ( r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_1737]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_2411,plain,
% 15.16/2.49      ( r2_hidden(sK0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))),k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 15.16/2.49      | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_2410]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1726,plain,
% 15.16/2.49      ( ~ r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))))
% 15.16/2.49      | k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_27]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1727,plain,
% 15.16/2.49      ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
% 15.16/2.49      | r1_tarski(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1641,plain,
% 15.16/2.49      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6)
% 15.16/2.49      | ~ r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)))
% 15.16/2.49      | k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1642,plain,
% 15.16/2.49      ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
% 15.16/2.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) != iProver_top
% 15.16/2.49      | r1_tarski(sK6,k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6))) != iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1600,plain,
% 15.16/2.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 15.16/2.49      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_28]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1601,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) != iProver_top
% 15.16/2.49      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X0) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_1600]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1603,plain,
% 15.16/2.49      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
% 15.16/2.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) = iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_1601]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_1602,plain,
% 15.16/2.49      ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
% 15.16/2.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)),sK6) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_1600]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_5,plain,
% 15.16/2.49      ( r1_tarski(X0,X0) ),
% 15.16/2.49      inference(cnf_transformation,[],[f110]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_103,plain,
% 15.16/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_105,plain,
% 15.16/2.49      ( r1_tarski(sK6,sK6) = iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_103]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_12,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 15.16/2.49      inference(cnf_transformation,[],[f116]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_90,plain,
% 15.16/2.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 15.16/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_92,plain,
% 15.16/2.49      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_90]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_91,plain,
% 15.16/2.49      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_22,plain,
% 15.16/2.49      ( X0 = X1
% 15.16/2.49      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 15.16/2.49      inference(cnf_transformation,[],[f102]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_62,plain,
% 15.16/2.49      ( k4_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK6,sK6,sK6,sK6)) = k2_enumset1(sK6,sK6,sK6,sK6)
% 15.16/2.49      | sK6 = sK6 ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_22]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_23,plain,
% 15.16/2.49      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 15.16/2.49      inference(cnf_transformation,[],[f121]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_61,plain,
% 15.16/2.49      ( k4_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK6,sK6,sK6,sK6)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
% 15.16/2.49      inference(instantiation,[status(thm)],[c_23]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(c_33,negated_conjecture,
% 15.16/2.49      ( k1_setfam_1(k2_enumset1(sK6,sK6,sK6,sK6)) != sK6 ),
% 15.16/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.16/2.49  
% 15.16/2.49  cnf(contradiction,plain,
% 15.16/2.49      ( $false ),
% 15.16/2.49      inference(minisat,
% 15.16/2.49                [status(thm)],
% 15.16/2.49                [c_47889,c_18888,c_8729,c_6984,c_6023,c_4056,c_3310,
% 15.16/2.49                 c_2411,c_2410,c_1727,c_1726,c_1642,c_1641,c_1603,c_1602,
% 15.16/2.49                 c_105,c_92,c_91,c_62,c_61,c_33]) ).
% 15.16/2.49  
% 15.16/2.49  
% 15.16/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.16/2.49  
% 15.16/2.49  ------                               Statistics
% 15.16/2.49  
% 15.16/2.49  ------ Selected
% 15.16/2.49  
% 15.16/2.49  total_time:                             1.656
% 15.16/2.49  
%------------------------------------------------------------------------------
