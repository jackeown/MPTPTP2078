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
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 173 expanded)
%              Number of clauses        :   35 (  37 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  348 ( 557 expanded)
%              Number of equality atoms :  169 ( 310 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f94,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f101,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f40])).

fof(f70,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f97,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f98,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f97])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_24,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1851,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_24,c_9])).

cnf(c_429,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_12049,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1851,c_429])).

cnf(c_12063,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r1_tarski(sK4,sK4)
    | sK4 != sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_12049])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4969,plain,
    ( ~ r1_tarski(X0,sK3(k2_enumset1(sK4,sK4,sK4,sK4),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4971,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4969])).

cnf(c_428,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_427,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2103,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_428,c_427])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1483,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_17])).

cnf(c_1714,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_1483,c_9])).

cnf(c_2361,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2103,c_1714])).

cnf(c_25,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2374,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2361,c_25])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1058,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_1591,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_1595,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1034,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1023,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1025,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_76,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_57,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_54,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12063,c_4971,c_2374,c_1595,c_1034,c_1025,c_76,c_57,c_54,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:59:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.81/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.98  
% 3.81/0.98  ------  iProver source info
% 3.81/0.98  
% 3.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.98  git: non_committed_changes: false
% 3.81/0.98  git: last_make_outside_of_git: false
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  ------ Parsing...
% 3.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  ------ Proving...
% 3.81/0.98  ------ Problem Properties 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  clauses                                 25
% 3.81/0.98  conjectures                             1
% 3.81/0.98  EPR                                     3
% 3.81/0.98  Horn                                    17
% 3.81/0.98  unary                                   8
% 3.81/0.98  binary                                  5
% 3.81/0.98  lits                                    55
% 3.81/0.98  lits eq                                 21
% 3.81/0.98  fd_pure                                 0
% 3.81/0.98  fd_pseudo                               0
% 3.81/0.98  fd_cond                                 2
% 3.81/0.98  fd_pseudo_cond                          8
% 3.81/0.98  AC symbols                              0
% 3.81/0.98  
% 3.81/0.98  ------ Input Options Time Limit: Unbounded
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  Current options:
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS status Theorem for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  fof(f11,axiom,(
% 3.81/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f16,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f11])).
% 3.81/0.98  
% 3.81/0.98  fof(f17,plain,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.81/0.98    inference(flattening,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f38,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f39,plain,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f38])).
% 3.81/0.98  
% 3.81/0.98  fof(f68,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f39])).
% 3.81/0.98  
% 3.81/0.98  fof(f3,axiom,(
% 3.81/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f25,plain,(
% 3.81/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.81/0.98    inference(nnf_transformation,[],[f3])).
% 3.81/0.98  
% 3.81/0.98  fof(f26,plain,(
% 3.81/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.81/0.98    inference(rectify,[],[f25])).
% 3.81/0.98  
% 3.81/0.98  fof(f27,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f28,plain,(
% 3.81/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.81/0.98  
% 3.81/0.98  fof(f48,plain,(
% 3.81/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f5,axiom,(
% 3.81/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f58,plain,(
% 3.81/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f6,axiom,(
% 3.81/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f59,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f6])).
% 3.81/0.98  
% 3.81/0.98  fof(f7,axiom,(
% 3.81/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f60,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f7])).
% 3.81/0.98  
% 3.81/0.98  fof(f71,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.81/0.98    inference(definition_unfolding,[],[f59,f60])).
% 3.81/0.98  
% 3.81/0.98  fof(f72,plain,(
% 3.81/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.81/0.98    inference(definition_unfolding,[],[f58,f71])).
% 3.81/0.98  
% 3.81/0.98  fof(f76,plain,(
% 3.81/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.81/0.98    inference(definition_unfolding,[],[f48,f72])).
% 3.81/0.98  
% 3.81/0.98  fof(f94,plain,(
% 3.81/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.81/0.98    inference(equality_resolution,[],[f76])).
% 3.81/0.98  
% 3.81/0.98  fof(f69,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f39])).
% 3.81/0.98  
% 3.81/0.98  fof(f1,axiom,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f14,plain,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f1])).
% 3.81/0.98  
% 3.81/0.98  fof(f19,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/0.98    inference(nnf_transformation,[],[f14])).
% 3.81/0.98  
% 3.81/0.98  fof(f20,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/0.98    inference(rectify,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f21,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f22,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f42,plain,(
% 3.81/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f22])).
% 3.81/0.98  
% 3.81/0.98  fof(f8,axiom,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f34,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.81/0.98    inference(nnf_transformation,[],[f8])).
% 3.81/0.98  
% 3.81/0.98  fof(f35,plain,(
% 3.81/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.81/0.98    inference(flattening,[],[f34])).
% 3.81/0.98  
% 3.81/0.98  fof(f62,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.81/0.98    inference(cnf_transformation,[],[f35])).
% 3.81/0.98  
% 3.81/0.98  fof(f84,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 3.81/0.98    inference(definition_unfolding,[],[f62,f72])).
% 3.81/0.98  
% 3.81/0.98  fof(f101,plain,(
% 3.81/0.98    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.81/0.98    inference(equality_resolution,[],[f84])).
% 3.81/0.98  
% 3.81/0.98  fof(f12,conjecture,(
% 3.81/0.98    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f13,negated_conjecture,(
% 3.81/0.98    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.81/0.98    inference(negated_conjecture,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f18,plain,(
% 3.81/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.81/0.98    inference(ennf_transformation,[],[f13])).
% 3.81/0.98  
% 3.81/0.98  fof(f40,plain,(
% 3.81/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f41,plain,(
% 3.81/0.98    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f40])).
% 3.81/0.98  
% 3.81/0.98  fof(f70,plain,(
% 3.81/0.98    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.81/0.98    inference(cnf_transformation,[],[f41])).
% 3.81/0.98  
% 3.81/0.98  fof(f89,plain,(
% 3.81/0.98    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 3.81/0.98    inference(definition_unfolding,[],[f70,f72])).
% 3.81/0.98  
% 3.81/0.98  fof(f2,axiom,(
% 3.81/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f23,plain,(
% 3.81/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/0.98    inference(nnf_transformation,[],[f2])).
% 3.81/0.98  
% 3.81/0.98  fof(f24,plain,(
% 3.81/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.81/0.98    inference(flattening,[],[f23])).
% 3.81/0.98  
% 3.81/0.98  fof(f47,plain,(
% 3.81/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f10,axiom,(
% 3.81/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f15,plain,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 3.81/0.98    inference(ennf_transformation,[],[f10])).
% 3.81/0.98  
% 3.81/0.98  fof(f67,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f15])).
% 3.81/0.98  
% 3.81/0.98  fof(f45,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f91,plain,(
% 3.81/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.81/0.98    inference(equality_resolution,[],[f45])).
% 3.81/0.98  
% 3.81/0.98  fof(f4,axiom,(
% 3.81/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f29,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.81/0.98    inference(nnf_transformation,[],[f4])).
% 3.81/0.98  
% 3.81/0.98  fof(f30,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.81/0.98    inference(flattening,[],[f29])).
% 3.81/0.98  
% 3.81/0.98  fof(f31,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.81/0.98    inference(rectify,[],[f30])).
% 3.81/0.98  
% 3.81/0.98  fof(f32,plain,(
% 3.81/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f33,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 3.81/0.98  
% 3.81/0.98  fof(f53,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.81/0.98    inference(cnf_transformation,[],[f33])).
% 3.81/0.98  
% 3.81/0.98  fof(f81,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.81/0.98    inference(definition_unfolding,[],[f53,f71])).
% 3.81/0.98  
% 3.81/0.98  fof(f97,plain,(
% 3.81/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.81/0.98    inference(equality_resolution,[],[f81])).
% 3.81/0.98  
% 3.81/0.98  fof(f98,plain,(
% 3.81/0.98    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.81/0.98    inference(equality_resolution,[],[f97])).
% 3.81/0.98  
% 3.81/0.98  fof(f52,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.81/0.98    inference(cnf_transformation,[],[f33])).
% 3.81/0.98  
% 3.81/0.98  fof(f82,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.81/0.98    inference(definition_unfolding,[],[f52,f71])).
% 3.81/0.98  
% 3.81/0.98  fof(f99,plain,(
% 3.81/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.81/0.98    inference(equality_resolution,[],[f82])).
% 3.81/0.98  
% 3.81/0.98  cnf(c_24,plain,
% 3.81/0.98      ( r2_hidden(sK3(X0,X1),X0)
% 3.81/0.98      | r1_tarski(X1,k1_setfam_1(X0))
% 3.81/0.98      | k1_xboole_0 = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.81/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1851,plain,
% 3.81/0.98      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 3.81/0.98      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 3.81/0.98      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_24,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_429,plain,
% 3.81/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.81/0.98      theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_12049,plain,
% 3.81/0.98      ( ~ r1_tarski(X0,X1)
% 3.81/0.98      | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X3))
% 3.81/0.98      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 3.81/0.98      | X2 != X0
% 3.81/0.98      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_1851,c_429]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_12063,plain,
% 3.81/0.98      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.81/0.98      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.81/0.98      | ~ r1_tarski(sK4,sK4)
% 3.81/0.98      | sK4 != sK4
% 3.81/0.98      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_12049]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_23,plain,
% 3.81/0.98      ( ~ r1_tarski(X0,sK3(X1,X0))
% 3.81/0.98      | r1_tarski(X0,k1_setfam_1(X1))
% 3.81/0.98      | k1_xboole_0 = X1 ),
% 3.81/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4969,plain,
% 3.81/0.98      ( ~ r1_tarski(X0,sK3(k2_enumset1(sK4,sK4,sK4,sK4),X0))
% 3.81/0.98      | r1_tarski(X0,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.81/0.98      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4971,plain,
% 3.81/0.98      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.81/0.98      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.81/0.98      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_4969]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_428,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_427,plain,( X0 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2103,plain,
% 3.81/0.98      ( X0 != X1 | X1 = X0 ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_428,c_427]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_17,plain,
% 3.81/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1483,plain,
% 3.81/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
% 3.81/0.98      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_2,c_17]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1714,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k1_xboole_0) | X0 = X1 ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_1483,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2361,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k1_xboole_0) | X1 = X0 ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_2103,c_1714]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_25,negated_conjecture,
% 3.81/0.98      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 3.81/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2374,plain,
% 3.81/0.98      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_2361,c_25]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_430,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.81/0.98      theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1058,plain,
% 3.81/0.98      ( r2_hidden(X0,X1)
% 3.81/0.98      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 3.81/0.98      | X0 != X2
% 3.81/0.98      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_430]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1591,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 3.81/0.98      | r2_hidden(X1,k1_xboole_0)
% 3.81/0.98      | X1 != X0
% 3.81/0.98      | k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1058]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1595,plain,
% 3.81/0.98      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.81/0.98      | r2_hidden(sK4,k1_xboole_0)
% 3.81/0.98      | sK4 != sK4
% 3.81/0.98      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3,plain,
% 3.81/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1034,plain,
% 3.81/0.98      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 3.81/0.98      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.81/0.98      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_22,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1023,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 3.81/0.98      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1025,plain,
% 3.81/0.98      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.81/0.98      | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5,plain,
% 3.81/0.98      ( r1_tarski(X0,X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_76,plain,
% 3.81/0.98      ( r1_tarski(sK4,sK4) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_14,plain,
% 3.81/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_57,plain,
% 3.81/0.98      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_15,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.81/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_54,plain,
% 3.81/0.98      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(contradiction,plain,
% 3.81/0.98      ( $false ),
% 3.81/0.98      inference(minisat,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_12063,c_4971,c_2374,c_1595,c_1034,c_1025,c_76,c_57,
% 3.81/0.98                 c_54,c_25]) ).
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  ------                               Statistics
% 3.81/0.98  
% 3.81/0.98  ------ Selected
% 3.81/0.98  
% 3.81/0.98  total_time:                             0.385
% 3.81/0.98  
%------------------------------------------------------------------------------
