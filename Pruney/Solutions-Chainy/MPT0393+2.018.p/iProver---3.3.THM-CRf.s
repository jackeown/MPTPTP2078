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
% DateTime   : Thu Dec  3 11:41:36 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 501 expanded)
%              Number of clauses        :   49 ( 101 expanded)
%              Number of leaves         :   19 ( 148 expanded)
%              Depth                    :   22
%              Number of atoms          :  412 (2446 expanded)
%              Number of equality atoms :  188 (1191 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f38])).

fof(f71,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f88,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f93,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f94,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f93])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f70])).

fof(f101,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f97,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1103,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X0))
    | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1634,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
    | r2_hidden(X0,k1_setfam_1(X2))
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),k1_setfam_1(X2)) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_20204,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_setfam_1(X0))
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_20210,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_setfam_1(k1_xboole_0))
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_20204])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1,X2),X2)
    | r2_hidden(sK2(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6308,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

cnf(c_23,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | ~ r2_hidden(sK2(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6651,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6308,c_23])).

cnf(c_6686,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(factoring,[status(thm)],[c_6308])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1152,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1340,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_6689,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6686,c_1340])).

cnf(c_6938,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6689,c_23])).

cnf(c_6941,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6651,c_28,c_6938])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6957,plain,
    ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6941,c_11])).

cnf(c_415,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_414,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1741,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_415,c_414])).

cnf(c_7839,plain,
    ( sK5 = sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6957,c_1741])).

cnf(c_416,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_20,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2762,plain,
    ( r1_tarski(X0,k1_setfam_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_416,c_20])).

cnf(c_7865,plain,
    ( ~ r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k1_xboole_0)
    | r1_tarski(sK5,k1_setfam_1(k1_xboole_0))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_7839,c_2762])).

cnf(c_417,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7845,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X1,sK5)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6957,c_417])).

cnf(c_8995,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_7845,c_414])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11056,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_8995,c_22])).

cnf(c_11532,plain,
    ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7865,c_28,c_1340,c_6686,c_11056])).

cnf(c_11545,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11532,c_1741])).

cnf(c_20024,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11545,c_2762])).

cnf(c_2766,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_416,c_414])).

cnf(c_5148,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2766,c_20])).

cnf(c_5150,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5148])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1491,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_2557,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_11,c_1491])).

cnf(c_3023,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2557,c_1741])).

cnf(c_3350,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3023,c_28])).

cnf(c_1394,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2430,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k1_setfam_1(X1))
    | ~ r1_tarski(k1_setfam_1(X1),X0) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_2441,plain,
    ( ~ r2_hidden(sK5,k1_setfam_1(k1_xboole_0))
    | r2_hidden(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_80,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20210,c_20024,c_5150,c_3350,c_2441,c_1340,c_80])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.25/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.49  
% 7.25/1.49  ------  iProver source info
% 7.25/1.49  
% 7.25/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.49  git: non_committed_changes: false
% 7.25/1.49  git: last_make_outside_of_git: false
% 7.25/1.49  
% 7.25/1.49  ------ 
% 7.25/1.49  ------ Parsing...
% 7.25/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.49  ------ Proving...
% 7.25/1.49  ------ Problem Properties 
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  clauses                                 27
% 7.25/1.49  conjectures                             1
% 7.25/1.49  EPR                                     3
% 7.25/1.49  Horn                                    15
% 7.25/1.49  unary                                   9
% 7.25/1.49  binary                                  4
% 7.25/1.49  lits                                    65
% 7.25/1.49  lits eq                                 27
% 7.25/1.49  fd_pure                                 0
% 7.25/1.49  fd_pseudo                               0
% 7.25/1.49  fd_cond                                 3
% 7.25/1.49  fd_pseudo_cond                          10
% 7.25/1.49  AC symbols                              0
% 7.25/1.49  
% 7.25/1.49  ------ Input Options Time Limit: Unbounded
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  ------ 
% 7.25/1.49  Current options:
% 7.25/1.49  ------ 
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  ------ Proving...
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  % SZS status Theorem for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  fof(f1,axiom,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f13,plain,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.25/1.49    inference(ennf_transformation,[],[f1])).
% 7.25/1.49  
% 7.25/1.49  fof(f16,plain,(
% 7.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.25/1.49    inference(nnf_transformation,[],[f13])).
% 7.25/1.49  
% 7.25/1.49  fof(f17,plain,(
% 7.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.25/1.49    inference(rectify,[],[f16])).
% 7.25/1.49  
% 7.25/1.49  fof(f18,plain,(
% 7.25/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f19,plain,(
% 7.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 7.25/1.49  
% 7.25/1.49  fof(f40,plain,(
% 7.25/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f19])).
% 7.25/1.49  
% 7.25/1.49  fof(f10,axiom,(
% 7.25/1.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f14,plain,(
% 7.25/1.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 7.25/1.49    inference(ennf_transformation,[],[f10])).
% 7.25/1.49  
% 7.25/1.49  fof(f32,plain,(
% 7.25/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.25/1.49    inference(nnf_transformation,[],[f14])).
% 7.25/1.49  
% 7.25/1.49  fof(f33,plain,(
% 7.25/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.25/1.49    inference(rectify,[],[f32])).
% 7.25/1.49  
% 7.25/1.49  fof(f36,plain,(
% 7.25/1.49    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0)))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f35,plain,(
% 7.25/1.49    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))) )),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f34,plain,(
% 7.25/1.49    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK2(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1))))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f37,plain,(
% 7.25/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 7.25/1.49  
% 7.25/1.49  fof(f66,plain,(
% 7.25/1.49    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.25/1.49    inference(cnf_transformation,[],[f37])).
% 7.25/1.49  
% 7.25/1.49  fof(f11,conjecture,(
% 7.25/1.49    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f12,negated_conjecture,(
% 7.25/1.49    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.25/1.49    inference(negated_conjecture,[],[f11])).
% 7.25/1.49  
% 7.25/1.49  fof(f15,plain,(
% 7.25/1.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.25/1.49    inference(ennf_transformation,[],[f12])).
% 7.25/1.49  
% 7.25/1.49  fof(f38,plain,(
% 7.25/1.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f39,plain,(
% 7.25/1.49    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f38])).
% 7.25/1.49  
% 7.25/1.49  fof(f71,plain,(
% 7.25/1.49    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.25/1.49    inference(cnf_transformation,[],[f39])).
% 7.25/1.49  
% 7.25/1.49  fof(f4,axiom,(
% 7.25/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f52,plain,(
% 7.25/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f4])).
% 7.25/1.49  
% 7.25/1.49  fof(f5,axiom,(
% 7.25/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f53,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f5])).
% 7.25/1.49  
% 7.25/1.49  fof(f6,axiom,(
% 7.25/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f54,plain,(
% 7.25/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f6])).
% 7.25/1.49  
% 7.25/1.49  fof(f72,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.25/1.49    inference(definition_unfolding,[],[f53,f54])).
% 7.25/1.49  
% 7.25/1.49  fof(f73,plain,(
% 7.25/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.25/1.49    inference(definition_unfolding,[],[f52,f72])).
% 7.25/1.49  
% 7.25/1.49  fof(f88,plain,(
% 7.25/1.49    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 7.25/1.49    inference(definition_unfolding,[],[f71,f73])).
% 7.25/1.49  
% 7.25/1.49  fof(f67,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.25/1.49    inference(cnf_transformation,[],[f37])).
% 7.25/1.49  
% 7.25/1.49  fof(f3,axiom,(
% 7.25/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f22,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.25/1.49    inference(nnf_transformation,[],[f3])).
% 7.25/1.49  
% 7.25/1.49  fof(f23,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.25/1.49    inference(flattening,[],[f22])).
% 7.25/1.49  
% 7.25/1.49  fof(f24,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.25/1.49    inference(rectify,[],[f23])).
% 7.25/1.49  
% 7.25/1.49  fof(f25,plain,(
% 7.25/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f26,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.25/1.49  
% 7.25/1.49  fof(f47,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.25/1.49    inference(cnf_transformation,[],[f26])).
% 7.25/1.49  
% 7.25/1.49  fof(f78,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.25/1.49    inference(definition_unfolding,[],[f47,f72])).
% 7.25/1.49  
% 7.25/1.49  fof(f93,plain,(
% 7.25/1.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.25/1.49    inference(equality_resolution,[],[f78])).
% 7.25/1.49  
% 7.25/1.49  fof(f94,plain,(
% 7.25/1.49    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.25/1.49    inference(equality_resolution,[],[f93])).
% 7.25/1.49  
% 7.25/1.49  fof(f46,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.25/1.49    inference(cnf_transformation,[],[f26])).
% 7.25/1.49  
% 7.25/1.49  fof(f79,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.25/1.49    inference(definition_unfolding,[],[f46,f72])).
% 7.25/1.49  
% 7.25/1.49  fof(f95,plain,(
% 7.25/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.25/1.49    inference(equality_resolution,[],[f79])).
% 7.25/1.49  
% 7.25/1.49  fof(f70,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 7.25/1.49    inference(cnf_transformation,[],[f37])).
% 7.25/1.49  
% 7.25/1.49  fof(f100,plain,(
% 7.25/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 7.25/1.49    inference(equality_resolution,[],[f70])).
% 7.25/1.49  
% 7.25/1.49  fof(f101,plain,(
% 7.25/1.49    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 7.25/1.49    inference(equality_resolution,[],[f100])).
% 7.25/1.49  
% 7.25/1.49  fof(f68,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.25/1.49    inference(cnf_transformation,[],[f37])).
% 7.25/1.49  
% 7.25/1.49  fof(f7,axiom,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f27,plain,(
% 7.25/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.25/1.49    inference(nnf_transformation,[],[f7])).
% 7.25/1.49  
% 7.25/1.49  fof(f28,plain,(
% 7.25/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.25/1.49    inference(flattening,[],[f27])).
% 7.25/1.49  
% 7.25/1.49  fof(f56,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 7.25/1.49    inference(cnf_transformation,[],[f28])).
% 7.25/1.49  
% 7.25/1.49  fof(f81,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 7.25/1.49    inference(definition_unfolding,[],[f56,f73])).
% 7.25/1.49  
% 7.25/1.49  fof(f97,plain,(
% 7.25/1.49    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.25/1.49    inference(equality_resolution,[],[f81])).
% 7.25/1.49  
% 7.25/1.49  fof(f2,axiom,(
% 7.25/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.25/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f20,plain,(
% 7.25/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.49    inference(nnf_transformation,[],[f2])).
% 7.25/1.49  
% 7.25/1.49  fof(f21,plain,(
% 7.25/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.49    inference(flattening,[],[f20])).
% 7.25/1.49  
% 7.25/1.49  fof(f43,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.25/1.49    inference(cnf_transformation,[],[f21])).
% 7.25/1.49  
% 7.25/1.49  fof(f90,plain,(
% 7.25/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.25/1.49    inference(equality_resolution,[],[f43])).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.25/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1103,plain,
% 7.25/1.49      ( r2_hidden(X0,X1)
% 7.25/1.49      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X0))
% 7.25/1.49      | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1634,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
% 7.25/1.49      | r2_hidden(X0,k1_setfam_1(X2))
% 7.25/1.49      | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),k1_setfam_1(X2)) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_1103]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_20204,plain,
% 7.25/1.49      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | r2_hidden(sK5,k1_setfam_1(X0))
% 7.25/1.49      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(X0)) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_1634]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_20210,plain,
% 7.25/1.49      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | r2_hidden(sK5,k1_setfam_1(k1_xboole_0))
% 7.25/1.49      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(k1_xboole_0)) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_20204]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_24,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,X1)
% 7.25/1.49      | r2_hidden(sK2(X1,X2),X2)
% 7.25/1.49      | r2_hidden(sK2(X1,X2),X0)
% 7.25/1.49      | k1_setfam_1(X1) = X2
% 7.25/1.49      | k1_xboole_0 = X1 ),
% 7.25/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_28,negated_conjecture,
% 7.25/1.49      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 7.25/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6308,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 7.25/1.49      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_24,c_28]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_23,plain,
% 7.25/1.49      ( r2_hidden(sK3(X0,X1),X0)
% 7.25/1.49      | ~ r2_hidden(sK2(X0,X1),X1)
% 7.25/1.49      | k1_setfam_1(X0) = X1
% 7.25/1.49      | k1_xboole_0 = X0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6651,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 7.25/1.49      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_6308,c_23]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6686,plain,
% 7.25/1.49      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 7.25/1.49      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(factoring,[status(thm)],[c_6308]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_10,plain,
% 7.25/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1152,plain,
% 7.25/1.49      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,X0)) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1340,plain,
% 7.25/1.49      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_1152]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6689,plain,
% 7.25/1.49      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(global_propositional_subsumption,
% 7.25/1.49                [status(thm)],
% 7.25/1.49                [c_6686,c_1340]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6938,plain,
% 7.25/1.49      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_6689,c_23]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6941,plain,
% 7.25/1.49      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(global_propositional_subsumption,
% 7.25/1.49                [status(thm)],
% 7.25/1.49                [c_6651,c_28,c_6938]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_11,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.25/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6957,plain,
% 7.25/1.49      ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_6941,c_11]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_415,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_414,plain,( X0 = X0 ),theory(equality) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1741,plain,
% 7.25/1.49      ( X0 != X1 | X1 = X0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_415,c_414]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7839,plain,
% 7.25/1.49      ( sK5 = sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5)
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_6957,c_1741]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_416,plain,
% 7.25/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.25/1.49      theory(equality) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_20,plain,
% 7.25/1.49      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2762,plain,
% 7.25/1.49      ( r1_tarski(X0,k1_setfam_1(k1_xboole_0))
% 7.25/1.49      | ~ r1_tarski(X1,k1_xboole_0)
% 7.25/1.49      | X0 != X1 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_416,c_20]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7865,plain,
% 7.25/1.49      ( ~ r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k1_xboole_0)
% 7.25/1.49      | r1_tarski(sK5,k1_setfam_1(k1_xboole_0))
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_7839,c_2762]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_417,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.25/1.49      theory(equality) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7845,plain,
% 7.25/1.49      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 7.25/1.49      | ~ r2_hidden(X1,sK5)
% 7.25/1.49      | X0 != X1
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_6957,c_417]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_8995,plain,
% 7.25/1.49      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 7.25/1.49      | ~ r2_hidden(X0,sK5)
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_7845,c_414]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_22,plain,
% 7.25/1.49      ( ~ r2_hidden(sK2(X0,X1),X1)
% 7.25/1.49      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
% 7.25/1.49      | k1_setfam_1(X0) = X1
% 7.25/1.49      | k1_xboole_0 = X0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_11056,plain,
% 7.25/1.49      ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 7.25/1.49      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 7.25/1.49      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_8995,c_22]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_11532,plain,
% 7.25/1.49      ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.25/1.49      inference(global_propositional_subsumption,
% 7.25/1.49                [status(thm)],
% 7.25/1.49                [c_7865,c_28,c_1340,c_6686,c_11056]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_11545,plain,
% 7.25/1.49      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_11532,c_1741]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_20024,plain,
% 7.25/1.49      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_setfam_1(k1_xboole_0))
% 7.25/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_11545,c_2762]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2766,plain,
% 7.25/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_416,c_414]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5148,plain,
% 7.25/1.49      ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
% 7.25/1.49      | ~ r1_tarski(k1_xboole_0,X0) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_2766,c_20]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5150,plain,
% 7.25/1.49      ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
% 7.25/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_5148]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13,plain,
% 7.25/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1491,plain,
% 7.25/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
% 7.25/1.49      | ~ r2_hidden(X0,k1_xboole_0) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2557,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k1_xboole_0) | X0 = X1 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_11,c_1491]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_3023,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k1_xboole_0) | X1 = X0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_2557,c_1741]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_3350,plain,
% 7.25/1.49      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_3023,c_28]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1394,plain,
% 7.25/1.49      ( ~ r2_hidden(sK5,X0) | r2_hidden(sK5,X1) | ~ r1_tarski(X0,X1) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2430,plain,
% 7.25/1.49      ( r2_hidden(sK5,X0)
% 7.25/1.49      | ~ r2_hidden(sK5,k1_setfam_1(X1))
% 7.25/1.49      | ~ r1_tarski(k1_setfam_1(X1),X0) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_1394]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2441,plain,
% 7.25/1.49      ( ~ r2_hidden(sK5,k1_setfam_1(k1_xboole_0))
% 7.25/1.49      | r2_hidden(sK5,k1_xboole_0)
% 7.25/1.49      | ~ r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_2430]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5,plain,
% 7.25/1.49      ( r1_tarski(X0,X0) ),
% 7.25/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_80,plain,
% 7.25/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.25/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(contradiction,plain,
% 7.25/1.49      ( $false ),
% 7.25/1.49      inference(minisat,
% 7.25/1.49                [status(thm)],
% 7.25/1.49                [c_20210,c_20024,c_5150,c_3350,c_2441,c_1340,c_80]) ).
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  ------                               Statistics
% 7.25/1.49  
% 7.25/1.49  ------ Selected
% 7.25/1.49  
% 7.25/1.49  total_time:                             0.661
% 7.25/1.49  
%------------------------------------------------------------------------------
